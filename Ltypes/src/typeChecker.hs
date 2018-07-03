

data Type = TypeArrow Multiplicity Type Type | TBoolean deriving (Eq,Show)

data Multiplicity = One | Omega deriving (Show,Eq)

instance Num Multiplicity where
  _ + b   = Omega
  One * b = b
  b * One = b
  _ * _ = Omega
  fromInteger 1 = One
  fromInteger _ = Omega

instance Ord Multiplicity where
  compare w 1 = GT
  compare 1 w = LT

type Bind = (Name, Multiplicity, Type)

type Context = [Bind]

type Name = String
type Tag = String

type Alt = (Tag, [Name], Term)

data Term = Var Name | Lambda Bind Term | App Term Term | Case Term [Alt] | Contructor Tag [Term]

type ErroWrapper a = Either String a

bindIn :: Bind -> Context -> Bool
bindIn _ [] = False
bindIn (name, m, ty) ((name', _, _):tail) = name == name' || bindIn (name, m, ty
  ) tail

scaleCtx :: Multiplicity -> Context -> Context
scaleCtx x ctx = [(name, (m*x)
  , ty)|(name, m, ty) <- ctx]

addCtx :: Context -> Context -> Context
addCtx ctx1 ctx2 = [case x `look` ctx2 of Just (x',q',t') -> (x, q+q', t) ; Nothing -> (x,q,t) | (x,q,t)<-ctx1]

addCtx' :: Context -> Context -> Context
addCtx' ctx1 [] = ctx1
addCtx' [] ctx2 = ctx2
addCtx' ((x,m,t) : ctx1) ctx2 | (x,m,t) `bindIn` ctx2 = (x, Omega, t) : addCtx' ctx1 (deleteBind x ctx2)
                             | otherwise = (x,m,t) : addCtx' ctx1 ctx2


throw :: String -> ErroWrapper a
throw message = Left message

look :: Name -> Context -> Maybe Bind
look _ [] = Nothing
look lookUpName ((name,m,ty):tail) = if(lookUpName == name) then (Just (name,m,ty)) else look lookUpName tail

deleteBind :: Name -> Context -> Context
deleteBind lookUpName ctx = filter (\(x,q,ty)->x/=lookUpName) ctx

identity  = (Lambda ("x",1,TBoolean) (Var "x"))

identity' = (Lambda ("x",Omega,TBoolean) (Var "x"))

discard   = Lambda("y",Omega, TBoolean) (Lambda ("x",1

  ,TBoolean) (Var "y"))

app = (Lambda("foo",Omega, (TypeArrow Omega TBoolean TBoolean)))(Lambda("y",Omega, TBoolean)(App (Var "foo") (Var "y")))

--Advanced Topics in Types in Programming Languages Benjamin C. Pierce

--Má ideia definir a compatibilidade assim, caso a multiplicidade seja expandida

compatible :: Bind -> Context -> Bool
compatible (x,q,t) gama = case (x `look` gama) of Just (x',q',t') -> ((q `compatibleMult` q') && (t == t'))
                                                  Nothing          -> q == Omega


compatibleMult :: Multiplicity -> Multiplicity -> Bool
compatibleMult 1 1     = True
compatibleMult Omega _ = True
compatibleMult _ _     = False


check :: Term -> ErroWrapper (Context, Type)
check t = check_ [] t

check_ :: Context -> Term -> ErroWrapper (Context, Type)

check_ ctxIn (Var x) = case (look x ctxIn) of
                        Just (_,_,ty) -> return ([(x,1,ty)],ty)
                        Nothing       -> throw "Non defined var"

--    Gama,x:qA |-c t:B ; Gama' x:qA compatible Gama'
-- _________________________________________________ (ABS)
--
--     Gama |-c Lambda (x:qA) . t:A ->q B ; Gama'-x                                  
check_ gama (Lambda (x,q,a) t ) =  do{
  (ctx,b) <- check_ ((x,q,a):gama) t;
  let result = (TypeArrow q a b) in
  case look x ctx of 
    Just (x',q',t') -> if (x',q',t') `compatible` ctx then return (( x `deleteBind` ctx),result) else throw "type error"
    Nothing -> if(q == Omega) then return (ctx,result) else throw (x ++ " was discarded")
}                              

--        Gama |-c A ->q B ; Gama'   Gama |- u:A ; Delta
--  _______________________________________________________(APP)
--
--           Gama |-c t.u :B ; Gama' + q*Delta                         
check_ gama (App t u) = do{ 
                            (gama',(TypeArrow q a b)) <- check_ gama t;
                            (_,type2)                 <- check_ gama u;
                            let delta = gama' `addCtx` (q `scaleCtx` delta) in
                              if(a == type2) then return (delta, b) else throw "type error"                              
                          }

check_ _ _ = throw "pattern matching exausted"



