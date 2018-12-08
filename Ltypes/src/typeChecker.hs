
data Type = TypeArrow Multiplicity Type Type | TBoolean deriving (Eq,Show)

data Multiplicity = One | Omega deriving Show

instance Num Multiplicity where
  _ + b   = Omega
  One * b = b
  b * One = b
  _ * _ = Omega
  fromInteger n = if (n == 1) then One else Omega

instance Eq Multiplicity where
  1 == 1 = True
  1 == Omega = False
  Omega == 1 = False
  Omega == Omega = True

type Bind = (Name, Multiplicity, Type)

type Context = [Bind]

type Name = String

data Term = Var Name | Lambda Bind Term | App Term Term

type Tc a = Either String a

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

throw :: String -> Tc a
throw message = Left message

look :: Name -> Context -> Maybe Bind
look _ [] = Nothing
look lookUpName ((name,m,ty):tail) = if(lookUpName == name) then (Just (name,m,ty)) else look lookUpName tail

deleteBind :: Name -> Context -> Context
deleteBind lookUpName ctx = filter (\(x,q,ty)->x/=lookUpName) ctx

check :: Term -> Tc (Context, Type)
check (Var x) = let ctx = [(x,1,TBoolean)] in return (ctx,TBoolean)
check (Lambda (x,q,ty1) term ) =  do (ctx,ty2) <- check term;
                                      let result = TypeArrow q ty1 ty2 in
                                      case look x ctx of 
                                        Just (x',q',ty') -> 
                                          if (q == q') then
                                            if (ty1 == ty') then 
                                              return ((deleteBind x ctx),result) 
                                            else 
                                              throw ("Mismatched type. Expected" ++ show ty1 ++ "but found" ++ show ty')
                                          else throw "Wrong Multiplicity"
                                        Nothing -> if(q == Omega) then return (ctx,result) else throw "type error"   
                                  
                                  

                                 
check (App term1 term2) = do (ctx1,(TypeArrow q a b)) <- check term1;
                              (ctx2,type2) <- check term2;
                              let ctx = ctx1 `addCtx` (scaleCtx q ctx) in
                                if(a == type2) then return (ctx, b) else throw "type error"
