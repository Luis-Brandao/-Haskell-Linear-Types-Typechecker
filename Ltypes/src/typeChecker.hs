data Type = TypeArrow Multiplicity Type Type | TBoolean deriving (Eq,Show)

data Multiplicity = One | Omega deriving (Show,Eq)

instance Num Multiplicity where
  _ + b   = Omega
  One * b = b
  b * One = b
  _ * _ = Omega
  fromInteger 1 = One
  fromInteger _ = Omega

type Bind = (Name, Multiplicity, Type)

type Context = [Bind]

type Name = String

data Term = Var Name | Lambda Bind Term | App Term Term

type ErroWrapper a = Either String a

bindIn :: Bind -> Context -> Bool
bindIn _ [] = False
bindIn (name, m, ty) ((name', _, _):tail) = name == name' || bindIn (name, m, ty
  ) tail

scaleCtx :: Multiplicity -> Context -> Context
scaleCtx x ctx = [(name, (m*x)
  , ty)|(name, m, ty) <- ctx]

addCtx :: Context -> Context -> Context
addCtx ctx1 [] = ctx1
addCtx [] ctx2 = ctx2
addCtx ((x,m,t) : ctx1) ctx2 | (x,m,t) `bindIn` ctx2 = (x, Omega, t) : addCtx ctx1 (deleteBind x ctx2)
                             | otherwise = (x,m,t) : addCtx ctx1 ctx2

throw :: String -> ErroWrapper a
throw message = Left message

look :: Name -> Context -> Maybe Bind
look _ [] = Nothing
look lookUpName ((name,m,ty):tail) = if(lookUpName == name) then (Just (name,m,ty)) else look lookUpName tail

deleteBind :: Name -> Context -> Context
deleteBind lookUpName ctx = filter (\(x,q,ty)->x/=lookUpName) ctx

--Examples

identity  = (Lambda ("x",1,TBoolean) (Var "x"))

identity' = (Lambda ("x",Omega,TBoolean) (Var "x"))

discard   = Lambda("y",Omega, TBoolean) (Lambda ("x",1

  ,TBoolean) (Var "y"))


--Advanced Topics in Types in Programming Languages Benjamin C. Pierce

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

--    T,x:qA |-c t:B ; T' x:qA compatible T'
-- _________________________________________________ (ABS)
--
--     T |-c Lambda (x:qA) . t:A ->q B ; T'-x

check_ ctxIn (Lambda (x,q,ty1) term ) =  do{ 
                                          (ctx,ty2) <- check_ ((x,q,ty1):ctxIn) term;
                                          let result = (TypeArrow q ty1 ty2) in
                                          case look x ctx of 
                                            Just (x',q',ty') -> 
                                              if (compatibleMult q q') then
                                                if (ty1 == ty') then return ((deleteBind x ctx),result) 
                                                else throw ("Mismatched type. Expected" ++ show ty1 ++ " but found" ++ show ty')
                                              else throw "Wrong Multiplicity"
                                            Nothing -> if(q == Omega) then return (ctx,result) else throw (
                                              x ++ " was discarded")

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




