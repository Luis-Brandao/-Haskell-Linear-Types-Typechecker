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

type Tc a = Either String a

bindIn :: Bind -> Context -> Bool
bindIn _ [] = False
bindIn (name, m, ty) ((name', _, _):tail) = name == name' || bindIn (name, m, ty
  ) tail

scaleCtx :: Multiplicity -> Context -> Context
scaleCtx x ctx = [(name, (m*x)
  , ty)|(name, m, ty) <- ctx]

addCtx :: Context -> Context -> Context
addCtx ctx1 ctx2 = [case x `look` ctx2 of Just (x',q',t') -> (x, q+q', t) ; Nothing -> (x,q,t) | (x,q,t)<-ctx1]

throw :: String -> Tc a
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


checkTop :: Term -> Tc (Context, Type)
checkTop t = check [] t

check :: Context -> Term -> Tc (Context, Type)
check ctxIn (Var x) = case (look x ctxIn) of
                        Just (_,_,ty) -> return ([(x,1,ty)],ty)
                        Nothing       -> throw "Non defined var"

--    Gama,x:qA |-c t:B ; Gama' x:qA compatible Gama'
-- _________________________________________________ (ABS)
--
--     Gama |-c Lambda (x:qA) . t:A ->q B ; Gama'-x                                  
check ctxIn (Lambda (x,q,a) t ) =  do{
  (ctxOut,b) <- check ((x,q,a):ctxIn) t;
  let result = (TypeArrow q a b) in
  case look x ctxOut of 
    Just (x',q',t') -> if (x',q',t') `compatible` ctxOut then return (( x `deleteBind` ctxOut),result) else throw "type error"
    Nothing -> if(q == Omega) then return (ctxOut,result) else throw (x ++ " was discarded")
}                              

--        Gama |-c A ->q B ; Gama'   Gama |- u:A ; Delta
--  _______________________________________________________(APP)
--
--           Gama |-c t.u :B ; Gama' + q*Delta                         
check ctxIn (App t u) = do{ 
                            (_,(TypeArrow q a b)) <- check ctxIn t;
                            (gamma,type2)         <- check ctxIn u;
                            let result = ctxIn `addCtx` (q `scaleCtx` gamma) in
                              if(a == type2) then return (result, b) else throw "type error"                              
                          }

check _ _ = throw "pattern matching exausted"



