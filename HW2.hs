module HW2 (
    parse, -- reexport for easy terminal use
    foldAndPropagateConstants,
    assignCommonSubexprs,
    reducePoly
) where

import Expression
import Parser

-- My libraries for solution
import Data.List

-- Do not change the module definition and imports above! Feel free
-- to modify the parser, but please remember that it is just a helper
-- module and is not related to your grade. You should only submit
-- this file. Feel free to import other modules, especially Data.List!

foldAndPropagateConstants :: [(String, ExprV)] -> [(String, ExprV)]
foldAndPropagateConstants v = reverse (gunc v [] [])



--inorder to stop infinite recursive calls (because I need to reevaluate the current if the depths have changed. If I make a recursive call again then it wont terminate forever)
--to stop minus
func_1 :: ExprV -> ExprV
func_1 (UnaryOperation Minus (Leaf (Constant a))) = Leaf (Constant (-a))
func_1 (UnaryOperation Minus (Leaf (Variable a))) = (UnaryOperation Minus (Leaf (Variable a)))
func_1 (UnaryOperation Minus (a)) = (UnaryOperation Minus (a))

--to stop plus
func_2 :: ExprV -> ExprV
func_2 (BinaryOperation Plus (Leaf (Constant a)) (Leaf (Constant b))) = Leaf(Constant (a+b))
func_2 (BinaryOperation Plus a b) = (BinaryOperation Plus a b)

--to stop plus. Notice that plus and times implementatations are almost the same except + -> *
func_3 :: ExprV -> ExprV
func_3 (BinaryOperation Times (Leaf (Constant a)) (Leaf (Constant b))) = Leaf(Constant (a*b))
func_3 (BinaryOperation Times a b) = (BinaryOperation Times a b)

--caller func it recurses to depths and passes to func_1,2,3 at the top of the call. In order to avoid inf recursion I made a sub_program / procedure to handle this situation
func :: ExprV -> ExprV
func (Leaf a) = (Leaf a)
func (UnaryOperation Minus (Leaf (Constant a))) = Leaf (Constant (-a))
func (UnaryOperation Minus (Leaf (Variable a))) = (UnaryOperation Minus (Leaf (Variable a)))
func (UnaryOperation Minus (a)) =    let 
                                                    tmp_depth = func (a)
                                                 in func_1 (UnaryOperation Minus tmp_depth)
func (BinaryOperation Plus (Leaf (Constant a)) (Leaf (Constant b))) = Leaf(Constant (a+b))
func (BinaryOperation Plus a b) =   let 
                                        tmp1_depth = func a
                                        tmp2_depth = func b
                                     in func_2 (BinaryOperation Plus tmp1_depth tmp2_depth)
func (BinaryOperation Times (Leaf (Constant a)) (Leaf (Constant b))) = Leaf(Constant (a*b))
func (BinaryOperation Times a b) =   let 
                                        tmp1_depth = func a
                                        tmp2_depth = func b
                                     in func_3 (BinaryOperation Times tmp1_depth tmp2_depth)
--simply to int. It doesnt replace known variables

data Is_Found = A ExprV | Not_Found deriving Show -- used for 1. part and 2. part

find_get :: [([Char], ExprV)] -> [Char] -> Is_Found
find_get [] target = Not_Found
find_get (x:cst) target |  (fst x == target) && (is_constant (snd x)) =  A (snd x)
                        |  (fst x == target) && (not (is_constant (snd x))) = Not_Found
                        |  otherwise = find_get cst target

conv_IsFoundtoInt :: Is_Found -> Int
conv_IsFoundtoInt (A (Leaf (Constant a))) = a

conv_IsFoundtoExprV :: Is_Found -> ExprV
conv_IsFoundtoExprV (A (Leaf (Constant a))) = (Leaf (Constant a)) -- used for 1. part
conv_IsFoundtoExprV (A (Leaf (Variable a))) = (Leaf (Variable a)) -- added for 2. part


change_leaf :: ExprV -> Int -> String -> ExprV
change_leaf (Leaf (Constant a)) c target =   Leaf (Constant a)
change_leaf (Leaf (Variable a)) c target     |  target == a =  Leaf (Constant c) 
                                             |  otherwise   =  Leaf (Variable a)
change_leaf (BinaryOperation Plus (a) (b)) c target =    let 
                                                            tmp1_depth = change_leaf a c target
                                                            tmp2_depth = change_leaf b c target
                                                          in (BinaryOperation Plus (tmp1_depth) (tmp2_depth))
change_leaf (BinaryOperation Times (a) (b)) c target =    let 
                                                            tmp1_depth = change_leaf a c target
                                                            tmp2_depth = change_leaf b c target
                                                          in (BinaryOperation Times (tmp1_depth) (tmp2_depth))  
change_leaf (UnaryOperation Minus (a)) c target =    let 
                                                            tmp1_depth = change_leaf a c target
                                                          in (UnaryOperation Minus (tmp1_depth))                                                                                                                  
replaceConstants :: ExprV -> [([Char],Int)] -> ExprV
replaceConstants exp [] =  exp  
replaceConstants exp (x:cst) =   let 
                                    tmp_exp = change_leaf exp (snd x) (fst x)
                                  in replaceConstants tmp_exp cst

gunc :: [([Char], ExprV)] -> [([Char],Int)] -> [([Char], ExprV)] -> [([Char], ExprV)]
gunc [] cst res = res
gunc (x:l) cst res   =  let
                           tmp_exp = replaceConstants (snd x) cst
                           calc_exp = func tmp_exp
                        in if (is_constant calc_exp) then (gunc l (((fst x),(get_constant calc_exp)):cst) (((fst x), calc_exp):res))
                           else (gunc l (cst) (((fst x), calc_exp):res))

--True if leaf is constant
is_constant :: ExprV -> Bool
is_constant (Leaf (Constant a)) = True
is_constant a = False

--use with care, it only works if leaf is constant
get_constant :: ExprV -> Int
get_constant (Leaf (Constant a)) = a

--generates new name for an assignment package
generateName :: [(String, ExprV)] -> String
generateName assList = '$' : (show (length assList))

--determine if target exp is in the assignment list : return Data Is_Found
isInAssList :: [(String, ExprV)] -> ExprV -> Is_Found
isInAssList [] target = Not_Found
isInAssList (x:assList) target   |  (snd x) == target =  A (Leaf(Variable (fst x)))
                                 |  otherwise = isInAssList assList target

isInAssListBool :: [(String, ExprV)] -> ExprV -> Bool
isInAssListBool assList target   |  convFoundtoBool(isInAssList assList target)  = True
                                 |  otherwise = False
convFoundtoBool :: Is_Found -> Bool
convFoundtoBool Not_Found = False
convFoundtoBool a = True

--eger varsa call et yoksa error gelir
getFromAssList :: [(String, ExprV)] -> ExprV -> ExprV
getFromAssList assList target = conv_IsFoundtoExprV (isInAssList assList target)


{-
--reflist olusturulacak 
formRefCount assList refList exp res =       
formRefCount assList refList (BinaryOperation Plus  exp_a exp_b) res =    
-}
countPattern :: (String, ExprV) -> ExprV -> Int
countPattern ass (Leaf (Constant a)) = 0
countPattern ass (Leaf (Variable a))   |  a==(fst ass) = 1 
                                       |  otherwise = 0
countPattern ass (BinaryOperation Plus  exp_a exp_b)  |  (snd ass) == (BinaryOperation Plus  exp_a exp_b) = 1
                                                      |  otherwise =  (countPattern ass exp_a) + (countPattern ass exp_b)

countPattern ass (BinaryOperation Times  exp_a exp_b) |  (snd ass) == (BinaryOperation Times  exp_a exp_b) = 1
                                                      |  otherwise =  (countPattern ass exp_a) + (countPattern ass exp_b)   

countPattern ass (UnaryOperation Minus  exp_a)  |  (snd ass) == (UnaryOperation Minus  exp_a) = 1
                                                |  otherwise =  (countPattern ass exp_a) 
--diger operation lara extend edilmelidir


--patter exp 1 kez gecmisse redundant dir replace edilir / 1 den fazla gecmis ise gereklidir veya 0 kez gecmisse ass de yoktur zaten exp ayni kalir
replacePattern :: (String, ExprV) -> ExprV -> ExprV
replacePattern ass (Leaf (Variable a))    |  (fst ass) == a = (snd ass)
                                          |  otherwise = (Leaf (Variable a))
replacePattern ass (Leaf (Constant a)) = (Leaf (Constant a))
replacePattern ass (BinaryOperation Plus  exp_a exp_b) = (BinaryOperation Plus  (replacePattern ass exp_a) (replacePattern ass exp_b))
replacePattern ass (BinaryOperation Times  exp_a exp_b) = (BinaryOperation Times  (replacePattern ass exp_a) (replacePattern ass exp_b))
replacePattern ass (UnaryOperation Minus exp_a) = (UnaryOperation Minus  (replacePattern ass exp_a))

dependAssList :: [(String, ExprV)] -> (String, ExprV) -> Bool
dependAssList [] ass = False
dependAssList (x:assList) ass |  countPattern ass (snd x) >=1 = True
                              |  otherwise = dependAssList (assList) ass

--call etmeden assList i reverse et is bitince de bidaha reverse et
updateAssList :: [(String, ExprV)] -> ExprV -> [(String, ExprV)] -> ([(String, ExprV)], ExprV)
updateAssList [] exp finalAssList = (finalAssList, exp)
updateAssList (x:assList) exp finalAssList   |  (countPattern x exp <= 1) && not(dependAssList finalAssList x) = updateAssList assList (replacePattern x exp) finalAssList
                                             |  otherwise = updateAssList assList exp (x:finalAssList)
                                             -- dependency olusturuldu depend ettigi yoksa replace edilcek, tek sikinti naming den gelebilir 0 1 3 -> 2 silindi duzensiz listeleme ?
                                             -- alttaki yorumum yanlis counterexample cow da e2309672
                                             -- bu condition a gelince is bitmistir cunku artik bundan sonra butun assignmentlar gereklidir buna kadar dependency si vardir

-- tree de her level da assagindan paketlenmis expression i gelirse ona gore daha basit bir sekilde hem asslist olusturulur hem de resulting exp cikmis olur
form :: [(String, ExprV)] -> ExprV -> ([(String, ExprV)], ExprV)
form assList (Leaf a) = (assList, (Leaf a))
form assList (BinaryOperation Plus  exp_a exp_b)   |  (isInAssListBool assList (BinaryOperation Plus exp_a exp_b))  = (assList, getFromAssList assList (BinaryOperation Plus exp_a exp_b))
                                                   |  otherwise = let 
                                                                     tmp_a = form assList exp_a
                                                                     tmp_a_assList = fst tmp_a
                                                                     tmp_a_exp = snd tmp_a

                                                                     tmp_b = form tmp_a_assList exp_b
                                                                     tmp_b_assList = fst tmp_b
                                                                     tmp_b_exp = snd tmp_b

                                                                     tmp = (BinaryOperation Plus  tmp_a_exp tmp_b_exp)

                                                                     tmp_name = (generateName tmp_b_assList)

                                                                  in if (isInAssListBool tmp_b_assList tmp) then (assList, getFromAssList tmp_b_assList tmp)
                                                                     else (tmp_b_assList ++ [(tmp_name, tmp)], Leaf (Variable tmp_name))
                                                                     
form assList (BinaryOperation Times  exp_a exp_b)  |  (isInAssListBool assList (BinaryOperation Times exp_a exp_b))  = (assList, getFromAssList assList (BinaryOperation Times exp_a exp_b))
                                                   |  otherwise = let 
                                                                     tmp_a = form assList exp_a
                                                                     tmp_a_assList = fst tmp_a
                                                                     tmp_a_exp = snd tmp_a

                                                                     tmp_b = form tmp_a_assList exp_b
                                                                     tmp_b_assList = fst tmp_b
                                                                     tmp_b_exp = snd tmp_b

                                                                     tmp = (BinaryOperation Times  tmp_a_exp tmp_b_exp)

                                                                     tmp_name = (generateName tmp_b_assList)

                                                                  in if (isInAssListBool tmp_b_assList tmp) then (assList, getFromAssList tmp_b_assList tmp)
                                                                     else (tmp_b_assList ++ [(tmp_name, tmp)], Leaf (Variable tmp_name))

form assList (UnaryOperation Minus exp_a) |  (isInAssListBool assList (UnaryOperation Minus exp_a))  = (assList, getFromAssList assList (UnaryOperation Minus exp_a))
                                          |  otherwise = let 
                                                            tmp_a = form assList exp_a
                                                            tmp_a_assList = fst tmp_a
                                                            tmp_a_exp = snd tmp_a


                                                            tmp = (UnaryOperation Minus  tmp_a_exp)

                                                            tmp_name = (generateName tmp_a_assList)

                                                            in if (isInAssListBool tmp_a_assList tmp) then (assList, getFromAssList tmp_a_assList tmp)
                                                               else (tmp_a_assList ++ [(tmp_name, tmp)], Leaf (Variable tmp_name))                                                                     





assignCommonSubexprs :: ExprV -> ([(String, ExprV)], ExprV)
assignCommonSubexprs exp = let 
                              tmp=(form [] exp)
                           in updateAssList (reverse (fst tmp)) (snd tmp) []



distLaw :: ExprV -> ExprV
distLaw (Leaf a) = (Leaf a)
distLaw (UnaryOperation Minus exp_a) = distLaw(BinaryOperation Times (Leaf (Constant (-1))) (distLaw exp_a))
distLaw (BinaryOperation Times (BinaryOperation Plus exp_b exp_c) exp_a) = let 
                                                                              tmp_exp_a = distLaw exp_a
                                                                              tmp_exp_b = distLaw exp_b
                                                                              tmp_exp_c = distLaw exp_c
                                                                              tmp_1 = distLaw (BinaryOperation Times tmp_exp_a tmp_exp_b)
                                                                              tmp_2 = distLaw (BinaryOperation Times tmp_exp_a tmp_exp_c)
                                                                           in (BinaryOperation Plus tmp_1 tmp_2)
distLaw (BinaryOperation Times exp_a (BinaryOperation Plus exp_b exp_c)) = let 
                                                                              tmp_exp_a = distLaw exp_a
                                                                              tmp_exp_b = distLaw exp_b
                                                                              tmp_exp_c = distLaw exp_c
                                                                              tmp_1 = distLaw (BinaryOperation Times tmp_exp_a tmp_exp_b)
                                                                              tmp_2 = distLaw (BinaryOperation Times tmp_exp_a tmp_exp_c)
                                                                           in (BinaryOperation Plus tmp_1 tmp_2)
distLaw (BinaryOperation Times exp_a exp_b) =   let
                                                   tmp_1 = distLaw exp_a
                                                   tmp_2 = distLaw exp_b
                                                in distLawOnce (BinaryOperation Times tmp_1 tmp_2)
                                                -- distLaw olmaya uygun degilse, infinite recursive loop, kacinmak icin external function call edilecek -> distLawOnce
distLaw (BinaryOperation Plus (exp_a) (exp_b)) = (BinaryOperation Plus (distLaw exp_a) (distLaw exp_b)) 
-- eger distlaw applicable degilse sal

distLawOnce :: ExprV -> ExprV
distLawOnce (Leaf a) = (Leaf a)
distLawOnce (UnaryOperation Minus exp_a) = (BinaryOperation Times (Leaf (Constant (-1))) (distLaw exp_a))
distLawOnce (BinaryOperation Times (BinaryOperation Plus exp_b exp_c) exp_a) = let 
                                                                              tmp_exp_a = distLawOnce exp_a
                                                                              tmp_exp_b = distLawOnce exp_b
                                                                              tmp_exp_c = distLawOnce exp_c
                                                                              tmp_1 = distLawOnce (BinaryOperation Times tmp_exp_a tmp_exp_b)
                                                                              tmp_2 = distLawOnce (BinaryOperation Times tmp_exp_a tmp_exp_c)
                                                                           in (BinaryOperation Plus tmp_1 tmp_2)
distLawOnce (BinaryOperation Times exp_a (BinaryOperation Plus exp_b exp_c)) = let 
                                                                              tmp_exp_a = distLawOnce exp_a
                                                                              tmp_exp_b = distLawOnce exp_b
                                                                              tmp_exp_c = distLawOnce exp_c
                                                                              tmp_1 = distLawOnce (BinaryOperation Times tmp_exp_a tmp_exp_b)
                                                                              tmp_2 = distLawOnce (BinaryOperation Times tmp_exp_a tmp_exp_c)
                                                                           in (BinaryOperation Plus tmp_1 tmp_2)

distLawOnce (BinaryOperation Times exp_a exp_b) = (BinaryOperation Times exp_a exp_b)
distLawOnce (BinaryOperation Plus (exp_a) (exp_b)) = (BinaryOperation Plus (distLawOnce exp_a) (distLawOnce exp_b))



-- assumption distLaw applied times doesnt include exp containing plus
coefPow :: ExprV -> (Int, Int)   
coefPow (Leaf (Variable a)) = (1, 1) 
coefPow (Leaf (Constant a)) = (0, a)
coefPow (BinaryOperation Times exp_a exp_b) =   let 
                                                   tmp_a = coefPow exp_a
                                                   tmp_b = coefPow exp_b
                                                in ((fst tmp_a)+(fst tmp_b), (snd tmp_a)*(snd tmp_b))


sepPlus :: ExprV -> [(Int, Int)]
sepPlus (BinaryOperation Plus exp_a exp_b) = let 
                                                tmp_a = sepPlus exp_a 
                                                tmp_b = sepPlus exp_b
                                             in merge tmp_a tmp_b
sepPlus exp = [(coefPow exp)]

merge :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
merge tmp_a [] = tmp_a
merge tmp_a (x:tmp_b) = merge (updOrAdd tmp_a x) tmp_b

updOrAdd :: [(Int, Int)] -> (Int, Int) -> [(Int, Int)]
updOrAdd tmp_a x = updOrAddRec tmp_a x []

updOrAddRec :: [(Int, Int)] -> (Int, Int) -> [(Int, Int)] -> [(Int, Int)]
updOrAddRec [] x res = x:res
updOrAddRec (y:tmp) x res  |  fst y == fst x = tmp ++ ((fst x, snd y + snd x):res)
                           |  otherwise = updOrAddRec tmp x (y:res)

-- zero coeff listeden cikartir
coeffZero :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)] 
coeffZero [] res = res 
coeffZero (x:tmp) res   |  snd x == 0 = coeffZero tmp res 
                        |  otherwise   =  coeffZero tmp (x:res)

sortCPList :: [(Int, Int)] -> [(Int, Int)] 
sortCPList tmp = sort $ coeffZero tmp []

{- NOT USED                      
isInCPList :: [(Int, Int)] -> (Int, Int) -> Bool
isInCPList [] x = False
isInCPList (y:tmp) x |  (snd y)== (snd x)  =  True -- onemli olan pow larin ayni tutmasi
                     |  otherwise = isInCPList tmp x 
-}

-- liste bossa hicbir sey yok 
convPCListToExp :: [(Int, Int)] -> ExprV -> ExprV

convPCListToExp [] var = (Leaf (Constant 0)) -- hersey cancel ediliyorsa constant 0 sonuc polynom
convPCListToExp (x:tmp) var   |  tmp==[] = (convPCToExp x var)
                              |  otherwise = (BinaryOperation Plus (convPCListToExp tmp var) (convPCToExp x var))

convPCToExp :: (Int, Int) -> ExprV -> ExprV
convPCToExp x  var   = convPowToExp x var

convPowToExp :: (Int,Int) -> ExprV -> ExprV
convPowToExp x var   |  fst x==0 = (Leaf (Constant (snd x)))
                     |  fst x==1 && (snd x)==(-1) =  (UnaryOperation Minus var)
                     |  fst x==1 && (snd x) < (-1) = (BinaryOperation Times (Leaf (Constant (snd x))) var)
                     |  fst x==1 && (snd x)==1 = var
                     |  fst x==1 = (BinaryOperation Times (Leaf (Constant (snd x))) var)
                     |  (fst x)>1   =  (BinaryOperation Times (convPowToExp ((fst x)-1, snd x) var) var )

findVar :: ExprV -> Is_Found
findVar (Leaf (Variable (var))) = A (Leaf (Variable (var)))
findVar (Leaf (Constant a)) = Not_Found
findVar (BinaryOperation Times exp_a exp_b) =   let 
                                                   tmp_a = findVar exp_a
                                                   tmp_b = findVar exp_b
                                                in if (convFoundtoBool tmp_a) then tmp_a
                                                   else tmp_b
findVar (BinaryOperation Plus exp_a exp_b) =   let 
                                                   tmp_a = findVar exp_a
                                                   tmp_b = findVar exp_b
                                                in if (convFoundtoBool tmp_a) then tmp_a
                                                   else tmp_b
findVar (UnaryOperation Minus exp_a) = findVar exp_a

reducePoly :: ExprV -> ExprV
reducePoly exp =  let 
                     distLawExp = distLaw exp
                     sepPlusList = sepPlus distLawExp 
                     sortList = sortCPList sepPlusList

                     revSortList = reverse sortList -- hoca sola sikistirmali istedi benimki saga sikistirmali verdigi icin

                     varIsFound = findVar exp
                  in if (convFoundtoBool varIsFound) then (convPCListToExp revSortList (conv_IsFoundtoExprV varIsFound))
                     else (convPCListToExp revSortList (Leaf (Variable "x"))) -- var not found sa var yoktur constant expression dir dummy variable "x" calismasi icin verilir


-- an extra dummy variable, so as to not crash the GUI
notImpl :: ExprV
notImpl = Leaf $ Variable "Not Implemented"

