module PL3
--Propositional logic. Formas normales.
--mcb
where
import Data.List(nub)
--
--Variables ---------------------------------------------------------
--Un tipo de datos para variables:
type Variable= Int -- 0 representa "x0", 1 representa "x1", etc
--OTRAS opciones para definir Variable:
{-type Variable2= String
data Variable3= X | V Variable3 deriving (Eq,Show)
data Variable4= X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 deriving (Eq,Show) --Diez variables
--}
---------------------------------------------------------------------
--
--Formulas de la PL -------------------------------------------------
--Un tipo de datos para formulas de la PL:
data PL = Bot           --Constructor para bottom
        | Top           --Constructor para top
        | Var Variable  --Constructor de variables
        | Imp PL PL     --Constructor de implicaciones
        | Dis PL PL     --Constructor de disyunciones
        | Con PL PL     --Constructor de conjunciones
        | Neg PL        --Constructor de negaciones
        deriving (Eq,Show)
--
--Ejemplos de formulas:
f1 :: PL
f1= Imp (Var 1) (Var 2)     -- x1 implica x2
f2 :: PL
f2= (Var 1) `Dis` (Var 2)   -- x1 or x2
f3 :: PL
f3= Con (Var 1) (Var 2)     -- x1 and x2
f4 :: PL
f4= Neg f1                  -- not f1
f5 :: PL
f5= (f1 `Imp` f2) `Imp` (Neg f2 `Imp` Neg f1)
f6 :: PL
f6= Con (Var 1) (Neg (Var 1)) -- x1 and not(x1)
--
g1= Dis (Var 1) (Var 2)       -- x1 | x2
g1b= Dis g1 (Neg $ Var 1)     -- x1 | x2 | !x1
g2= Dis (Var 3) (Neg $ Var 4) -- x3 | !x4
g2b= Dis g2 (Neg $ Var 3)     --  x3 | !x4 | !x3
g3= Dis (Neg $ Var 3) (Var 4) -- !x3 | x4
g3b= Dis g3 (Var 3)           -- !x3 | x4 | x3
g4= Con g1 g2 --(x1 | x2) & (x3 | !x4)
g4b= Con g1b g2b -- (x1 | x2 | !x1) & (x3 | !x4 | !x3)
g5= Con g4 g3 -- ((x1 | x2) & (x3 | !x4)) & (!x3 | x4)
g6= Con g4b g3b --((x1 | x2 | !x1) & (x3 | !x4 | !x3) ) & (!x3 | x4 | x3)
--
---------------------------------------------------------------------
--
--Valuaciones (truth assignments) -----------------------------------
type Valuacion= Variable -> Int
{--Otras opciones para definir Valuacion: (En clase veremos una alternativa a las valuaciones)
type Modelo= [Variable] -- Los elementos son las variables verdaderas
--}
-- Ejemplos de valuaciones:
sigma1 :: Variable -> Int
sigma1 x= case x of
            0    -> 1 --"x0"
            1    -> 0 --"x1"
            _       -> error $ "sigma1 no esta definida para la variable x"++(show x)
--
sigma2 :: Variable -> Int
sigma2 _ = 0 --En sigma2 todas las variables son falsas
--
sigma3 :: Variable -> Int
sigma3 x= case x of
            0    -> 0 --"x0"
            _    -> 1 --Las demas variables son verdaderas en sigma3
---------------------------------------------------------------------
--Modelos (conjuntos de variables)
--Un tipo de datos para modelos:
--Util para la semantica de la PL mediante modelos, i.e. mediante conjuntos de variables.
type Modelo= [Variable] -- Un modelo es un conjunto de variables representado por una lista.
                        -- Intuitivamente, los elementos de un modelo son las variables verdaderas.
--Ejemplos de modelos:
m1 ::Modelo
m1= [0]     --x0 es la unica variable verdadera
m2 ::Modelo
m2= []      --ninguna variable es verdadera
m3 ::Modelo
m3= [1..]   --x1,x2,... son las variables verdaderas. "Infinito", pero solo usaremos modelos finitos.
m4 ::Modelo
m4= [2,4,6] --x2,x4,x6 son las variables verdaderas.
m5 ::Modelo
m5= [1]     --x1 es la unica variable verdadera
--
powerSet :: [a] -> [[a]]
--Calcula el conjunto potencia de un conjunto representado por una lista.
-- Por recursion sobre la estrutura de las listas, [a].
--Util para definir la semantica de la PL mediante modelos, i.e. mediante conjuntos de variables
powerSet []     =   [[]]                    -- conjunto potencia de []
powerSet (x:xs) =   powerSxs                -- conjunto potencia de xs
                    ++ (map (x:) powerSxs)  -- agregar x a los elementos de powerSxs
                    where powerSxs= (powerSet xs)
--
mSatisface :: Modelo-> PL -> Bool
-- mSatisface m phi implementa "m |= phi".
mSatisface m phi= case phi of -- Segun la estructura de phi:
        -- Casos base:
        Bot             -> False        --m no satisface bottom
        Top             -> True         --m satisface top
        Var x           -> x `elem` m   --m satisface x sii x pertenece a m
        -- Casos recursivos:
        Imp alpha beta  ->     not(mSatisface m alpha)  -- m no satisface a alpha
                            || (mSatisface m beta)      -- o m satisface a beta
        Dis alpha beta  ->     (mSatisface m alpha)     -- m satisface a alpha
                            || (mSatisface m beta)      -- o m satisface a beta
        Con alpha beta  ->     (mSatisface m alpha)     -- m satisface a alpha
                            && (mSatisface m beta)      -- y m satisface a beta
        Neg alpha       ->  not(mSatisface m alpha)     -- m no satisface a alpha
--
--Pruebas:
test_mSatisface :: [(String, Bool)]
-- En ghci usar: test_mSatisface
test_mSatisface= [
         ("mSatisface m5 f1: ", mSatisface m5 f1)
        ,("mSatisface m5 f2: ", mSatisface m5 f2)
        ,("mSatisface m5 f3: ", mSatisface m5 f3)
        ,("mSatisface m5 f4: ", mSatisface m5 f4)
        ,("mSatisface m5 f5: ", mSatisface m5 f5)
        ,("mSatisface m5 f6: ", mSatisface m5 f6)
        ]
--
varsOF :: PL -> [Variable]
--Lista de variables de phi
varsOF phi = case phi of
        -- Casos base:
        Bot             -> []
        Top             -> []
        Var x           -> [x]
        -- Casos recursivos:
        Imp alpha beta  -> nub (varsOF alpha ++(varsOF beta))
        Dis alpha beta  -> nub (varsOF alpha ++(varsOF beta))
        Con alpha beta  -> nub (varsOF alpha ++(varsOF beta))
        Neg alpha       -> varsOF alpha

--
inSAT :: PL -> Bool
-- Indica si phi es satisfactible o no.
-- En este caso la definicion NO es por recursion sobre phi.
inSAT phi =
    or                                  -- aplica "or" a una lista de valores booleanos
        [mSatisface m phi |             -- "mSatisface m phi" es un booleano
         m <- powerSet variablesDEphi]  -- m se toma de la lista de subconjuntos de variablesDEphi
    where
    --variablesDEphi= [1,2] -- Ejercicio: CORREGIR a: variablesDEphi= varsOF phi
    variablesDEphi= varsOF phi
--
--Pruebas:
test_inSAT :: [([Char], Bool)]
test_inSAT= [
     ("f1 in SAT: ", inSAT f1)
    ,("f2 in SAT: ", inSAT f2)
    ,("f3 in SAT: ", inSAT f3)
    ,("f4 in SAT: ", inSAT f4)
    ,("f5 in SAT: ", inSAT f5)
    ,("f6 in SAT: ", inSAT f6)
    ]
--
---------------------------------------------------------------------
--
--Ejercicio (hecho en clase, el jueves 10ago2017).
--Sea phi en PL. USANDO recursion sobre la estructura de phi,
--definir una funcion, cuentaAnds, que cuente el numero de operadores Con en phi.
--Por ejemplo, cuentaAnds (Dis Top Bot)= 0, cuentaAnds (Con Bot Top)=1
cuentaAnds :: PL -> Int
cuentaAnds phi = case phi of -- Segun la estructura de phi:
            Bot             -> 0 --Si phi=Bot
            Top             -> 0 --Si phi=Top
            Var _           -> 0 --Si phi es una variable
            Imp alpha beta  -> (cuentaAnds alpha)+ cuentaAnds(beta)     --Si phi=alpha -> beta
            Dis alpha beta  -> (cuentaAnds alpha)+ cuentaAnds(beta)     --Si phi=alpha | beta
            Con alpha beta  -> (cuentaAnds alpha)+ cuentaAnds(beta) + 1 --Si phi=alpha & beta
            Neg alpha       -> cuentaAnds alpha                         --Si phi= !alpha
--
showVar ::Variable -> String
--Transforma una variable n a un String. 0 se transforma a "x0", 1 a "x1", etc.
showVar x= if x>0
              then "x"++(show x)
              else error $ "showVar: las variables deben ser enteros no negativos"
--
--
{-Ejercicios PL1 [Ya deben estar resueltos].
    (USAR recursion sobre la estructura de phi. VER cuentaAnds)
1.  Definir una funcion, showPL, que transforme una formula phi de la PL en un String.
    Bot se debe transformar a "Bot", Top a "Bot, la variable 0 a "x0",
    El operador Imp se transforma a "->", Dis a "|", Con a "&", y Neg se transforma a "!".
2.  Definir una funcion, quitaTop, que reemplace, en una formula phi de la PL,
    los operadores Top por "Neg Bot"
3.  Definir una funcion, quitaImp, que reemplace, en una formula phi de la PL,
    los operadores Imp por una combinacion de Dis y Neg logicamente equivalente a Imp.
    f -> g = !f | g.
4.  Definir una función, f4, que transforme una formula phi en una formula phi' tal que:
    phi' es logicamente equivalente a phi, y phi' solo utiliza variables, Bot, Top, Dis, Con y Neg.
5.  Definir una función, f5, que transforme una formula phi en una formula phi' tal que:
    phi' es logicamente equivalente a phi, y phi' solo utiliza variables, Bot, Dis, y Neg.
6.  Definir una función, f6, que transforme una formula phi en una formula phi' tal que:
    phi' es logicamente equivalente a phi, y phi' solo utiliza variables, Top, Con, y Neg.
7.  Definir una función, f7, que transforme una formula phi en una formula phi' tal que:
    phi' es logicamente equivalente a phi, y phi' solo utiliza variables, Bot, Imp, y Neg.
8.  Definir una función, f8, que transforme una formula phi en una formula phi' tal que:
    phi' es logicamente equivalente a phi, y phi' solo utiliza variables, Bot e Imp.
9.  a) Defina un tipo de datos PL2 que, ademas de los constructores de PL,
    incluya un operador Nor.
    Extendienda la funcion showPL a una funcion showPL2 que considere el operador Nor.
10  Definir una función, f10, que transforme una formula phi en una formula phi' tal que:
    phi' es logicamente equivalente a phi, y phi' solo utiliza variables y Nor.
-}
--
{-Ejercicios PL2: -------------------------------------------------------------
1. Definir una funcion, varsOF, tal que:
   (varsOF phi) calcula la lista de variables que ocurren en la formula phi de la PL.
   Definir varsOF recursivamente sobre la estructura de phi.
   Evitar repeticiones usando la funcion "nub" de la biblioteca Data.List (import Data.List).
   Por ejemplo, varsOF f5=[1,2] (ver f5 aariba).
2. Corregir la funcion inSAT usando la funcion varsOF.
3. En forma analoga a la funcion inSAT, definir una funcion, inVAL,
   que indique si phi es una formula valida o no.
   (La funcion "and" aplica un or a una lista de valores booleanos)
4. a) Definir inVAL2 usando inSAT (usar la relacion entre validez y satisfactibilidad vista en clase)
   b) Definir inSAT2 usando inSAT (usar la relacion entre validez y satisfactibilidad)
5. Definir una funcion, impLogicamente, que indique si Gama implica logicamente a phi, o no.
   Representar los conjuntos de formulas con listas de formulas.
   Por ejemplo (impLogicamente [Var 1, Var 2] ((Var 1) `Con` (Var 2))) = True.
6. Definir una funcion, logEquivalentes, que indique si phi y psi son logicamente equivalentes.
   Usar impLogicamente.
   Por ejemplo (logEquivalentes (Var 1) (Neg(Neg(Var 1)))) = True.
-}
--
--
----------------------------------------------------------------------
-- Formas normales: --------------------------------------------------
--
showDisLit :: PL -> String
--Transforma una Disyuncion de literales a string
showDisLit phi= case phi of
    --Cero literales. Disyuncion sobre un conjunto vacio de literales, \bigvee \varnothing:
    Bot         -> "Bot" -- Convencion: Bot= \bigvee \varnothing= Disyuncion sobre vacio.
    --Un literal. Disyuncion sobre un conjunto de un literal:
    Var x       -> showVar x        -- Un literal positivo
    Neg (Var x) -> "!"++(showVar x) -- Un literal negativo
    --Mas de un literal. Disyuncion sobre un conjunto de mas de un literal:
    (Dis alpha beta)    -> "("++(showDisLit alpha)++" | "++(showDisLit beta)++")"
    _                   -> error $
            "showDisLit: phi no es una disyuncion sobre literales, phi="++(show phi)
--
showCNF :: PL -> String
--Transforma una formula en cnf a string
showCNF phi = case phi of
    Top         -> "Top" -- Convencion: Top= \bigwedge \varnothing= Conjuncion sobre vacio.
    --Una clausula. Conjuncion sobre un conjunto de una clausula:
    Var x       -> showVar x                --Una clausula con un literal positivo
    Neg (Var x) -> "!"++(showVar x)         --Una clausula con un literal negativo
    (Dis _ _)   -> showDisLit phi           --Una clausula con mas de un literal
    --Mas de una clausula. Conjuncion sobre un conjunto de mas de una clausula:
    (Con alpha beta) -> (showCNF alpha)++" & "++(showCNF beta)
    _                -> error $ "showCNF: phi no esta en CNF, phi="++(show phi)
--
disLit2ListLit :: PL -> [PL]
--Transforma una disyuncion sobre un conjunto de literales a un lista de literales.
--Ejemplos: (x3 | !x4) --> [x3,!x4], Bot ---> []
disLit2ListLit phi = case phi of
    --Cero literales. Disyuncion sobre un conjunto vacio de literales, \bigvee \varnothing:
    Bot         -> [] -- Convencion: Bot= \bigvee \varnothing= Disyuncion sobre vacio.
    --Un literal. Disyuncion sobre un conjunto de un literal:
    Var x       -> [Var x]       -- Un literal positivo
    Neg (Var x) -> [Neg (Var x)] -- Un literal negativo
    --Mas de un literal. Disyuncion sobre un conjunto de mas de un literal:
    (Dis alpha beta)    -> (disLit2ListLit alpha) ++ (disLit2ListLit beta)
    _                   -> error $
            "disLit2ListLit: phi no es una disyuncion de literales, phi="++(show phi)
--
cnf2LListLit :: PL -> [[PL]]
--Transforma una formula en CNF, i.e. una conjuncion sobre un conjunto de disyunciones de literales,
--a una lista de listas de literales.
--Ejemplos: (x1 | x2) & (x3 | !x4) ---> [[x1,x2], [x3,!x4]], Top ---> []
cnf2LListLit phi = case phi of
    --Cero clausulas. Conjuncion sobre un conjunto vacio de clausulas, \bigvee \varnothing:
    Top              -> [] -- Convencion: Top= \bigwedge \varnothing= Conjuncion sobre vacio.
    --Una clausula. Conjuncion sobre un conjunto de una clausula:
    Var x       -> [[Var x]]                    --Una clausula con un literal positivo
    Neg (Var x) -> [[Neg (Var x)]]              --Una clausula con un literal negativo
    (Dis _ _)   -> [disLit2ListLit phi]         --Una clausula con mas de un literal
    --Mas de una clausula. Conjuncion sobre un conjunto de mas de una clausula:
    (Con alpha beta) -> (cnf2LListLit alpha) ++ (cnf2LListLit beta)
    _                -> error $ "cnf2LListLit: phi no esta en CNF, phi="++(show phi)
--
--Tests:
--cnf2LListLit g1
--showCNF  g1
--cnf2LListLit g2
--showCNF  g2
--cnf2LListLit g3
--showCNF  g3
--cnf2LListLit g4
--showCNF  g4
--cnf2LListLit g5
--showCNF  g5
--
litComp :: PL -> PL
--Calcula el literal complementario de l
litComp phi= case phi of
                Var x         -> Neg (Var x)
                Neg (Var x)   -> Var x
                _ -> error $ "litComp: phi no es literal, phi="++(show phi)
--
clausulaTrue :: [PL] -> Bool
--Determina si una clausula (disyunncion sobre una lista de literales) ll es true
--ll es true sii ll tiene dos literales complementarios.
clausulaTrue ll= case ll of
                    []      -> False
                    (l:ls)  -> (litComp l) `elem` ll || clausulaTrue ls
--
--Tests:
--clausulaTrue [Var 1, Neg $ Var 1] True elemento de CNF
--clausulaTrue [Var 1, Neg $ Var 2] False elemento de DNF
--
clauListTrue :: [[PL]] -> Bool
--Determina si todas las clausulas (listas de literales) de una lista lc son true.
clauListTrue lc = case lc of
                    []      -> True
                    (c:cs)  -> clausulaTrue c && clauListTrue cs

--
--Tests:
--clauListTrue [[Var 1, Neg $ Var 1], [Var 1, Neg $ Var 2]]
--

decideCNFenVAL :: PL -> Bool
--Decide si una formula-CNF pertenece, o no, a VAL:={phi in PL | forall m: m |= phi}
--Se aplica el algoritmo visto en clase.
--Ideas basicas:
--      Para revisar clausulas y literales, phi se transforma en una lista de listas de literales.
--      Una clausula (lista de literales) C es valida sii C tiene un par de literales complementarios.
--      phi en CNF es valida sii todas las clausulas de phi son validas.
decideCNFenVAL phi = clauListTrue (cnf2LListLit phi)
--
--Tests en ghci:
--showCNF g5
--decideCNFenVAL g5
--inSAT g5
--inSAT (Neg g5)
--
--showCNF g6
--decideCNFenVAL g6
--inSAT g6
--inSAT (Neg g6)
--

---------------------------------------------------------------------------
-- Practica de Laboratorio 1: ---------------------------------------------
{-
1. Definir una funcion, decideDNFenSAT :: PL -> Bool, tal que:

a) Si phi es una formula en DNF, entonces
(decideDNFenSAT phi) es True sii phi es satisfactible.
Es decir, decideDNFenSAT debe decidir si una formula-CNF pertenece, o no, a SAT.
Recordar que SAT:={phi in PL | exists m: m |= phi}

b) decideDNFenSAT se define aplicando el algoritmo visto en clase para decidir
satisfactibilidad de formulas en DNF.

c) decideDNFenSAT es analogo a la funcion decideCNFenVAL incluida en este archivo Haskell.

d) decideDNFenSAT y, las funciones que ustedes definan, deben estar al
final de este archivo, a partir de la linea 380.

e) NO se permite modificar NINGUNA de las lineas anteriores a la linea 355.
-}
--
--Fecha de entrega: 10 de octubre de 2017 antes de las 11:59.
--Forma de trabajo: en equipos (Los mismos que tiene registrados Laura).
--El archivo debe incluir un lista comentada de los integrantes del equipo.
--Enviar el archivo con la solucion a Rafael CON copia para mi.
--Deben recibir un mensaje con un acuse de recibo.
--
-- Satisfactibidad de formulas en DNF:-------------------------------
--


----------------------------------------------------------------------
-- Formas normales: --------------------------------------------------
--


--
g10= Con (Var 1) (Var 2)       -- x1 & x2
g10b= Con g11 (Neg $ Var 1)     -- x1 & x2 & !x1
g11= Con (Var 3) (Neg $ Var 4) -- x3 & !x4
g11b= Con g22 (Neg $ Var 3)     --  x3 & !x4 & !x3
g12= Con (Neg $ Var 3) (Var 4) -- !x3 & x4
g12b= Con g33 (Var 3)           -- !x3 & x4 & x3
g13= Dis g11 g22 --(x1 & x2) | (x3 & !x4)
g13b= Dis g11b g22b -- (x1 & x2 & !x1) | (x3 & !x4 & !x3)
g15= Dis g44 g33 -- ((x1 & x2) | (x3 & !x4)) | (!x3 & x4)
g15= Dis g44b g33b

showConLit :: PL -> String
--Transforma una Conjuncion de literales a string
showConLit phi= case phi of
    --Cero literales. Disyuncion sobre un conjunto vacio de literales, \bigvee \varnothing:
    Bot         -> "Bot" -- Convencion: Bot= \bigvee \varnothing= Disyuncion sobre vacio.
    --Un literal. Disyuncion sobre un conjunto de un literal:
    Var x       -> showVar x        -- Un literal positivo
    Neg (Var x) -> "!"++(showVar x) -- Un literal negativo
    --Mas de un literal. Conjuncion sobre un conjunto de mas de un literal:
    (Con alpha beta)    -> "("++(showDisLit alpha)++" & "++(showDisLit beta)++")"
    _                   -> error $
            "showConLit: phi no es una conjuncion sobre literales, phi="++(show phi)
--
showDNF :: PL -> String
--Transforma una formula en dnf a string
showDNF phi = case phi of
      Top       -> "Top" -- Convencion: Top= \bigwedge \varnothing= Conjuncion sobre vacio.
      --Un termino. Disyncion sobre un conjunto de una terminos:
      Var x     -> showVar x--Un termino con un literal positivo
      Neg (Var x) -> "!"++(showVar x)--Un termino con un literal negativo
      (Con _ _)   -> showConLit phi  --Un termino con mas de un literal
      --Mas de un termino. Disyuncion sobre un conjunto de mas de un terminos:
      (Dis alpha beta) -> (showDNF alpha)++" |  "++(showDNF beta)
      _                -> error $ "showDNF: phi no esta en DNF, phi="++(show phi)
            --
--
--
conLit2ListLit :: PL -> [PL]
--Transforma una conjuncion sobre un conjunto de literales a un lista de literales.
--Ejemplos: (x3 | !x4) --> [x3,!x4], Bot ---> []
conLit2ListLit phi = case phi of
    --Cero literales. Conjuncion sobre un conjunto vacio de literales, \bigvee \varnothing:
    Bot         -> [] -- Convencion: Bot= \bigvee \varnothing= Conjuncion sobre vacio.
    --Un literal. Conjuncion sobre un conjunto de un literal:
    Var x       -> [Var x]       -- Un literal positivo
    Neg (Var x) -> [Neg (Var x)] -- Un literal negativo
    --Mas de un literal. Conjuncion sobre un conjunto de mas de un literal:
    (Con alpha beta)    -> (conLit2ListLit alpha) ++ (conLit2ListLit beta)
    _                   -> error $
            "conLit2ListLit: phi no es una conjuncion de literales, phi="++(show phi)
--

--
dnf2LListLit :: PL -> [[PL]]
--Transforma una formula en DNF, i.e. una disyuncion sobre un conjunto de conjunciones de literales,
--a una lista de listas de literales.
--Ejemplos: (x1 & x2) | (x3 & !x4) ---> [[x1,x2], [x3,!x4]], Top ---> []
dnf2LListLit phi = case phi of
    --Cero terminos. Disyuncion sobre un conjunto vacio de terminos, \bigvee \varnothing:
    Top              -> [] -- Convencion: Top= \bigwedge \varnothing= Disyuncion sobre vacio.
    --Un termino. Disyuncion sobre un conjunto de un termino:
    Var x       -> [[Var x]]                    --Un termino con un literal positivo
    Neg (Var x) -> [[Neg (Var x)]]              --Un termino con un literal negativo
    (Con _ _)   -> [conLit2ListLit phi]         --Un termino con mas de un literal
    --Mas de un termino. Disyuncion sobre un conjunto de mas de un termino:
    (Dis alpha beta) -> (dnf2LListLit alpha) ++ (dnf2LListLit beta)
    _                -> error $ "dnf2LListLit: phi no esta en DNF, phi="++(show phi)
--
--Tests:
--dnf2LListLit g10
--showDNF  g10
--dnf2LListLit g11
--showDNF  g11
--dnf2LListLit g13
--showDNF  g13
--dnf2LListLit g14
--showDNF  g14
--dnf2LListLit g15
--showDNF  g15
--

terminoTrue :: [PL] -> Bool
--Determina si una termino (conjuncion sobre una lista de literales) ll es true
--ll es true sii ll tiene dos literales complementarios.
terminoTrue ll= case ll of
                    []      -> False
                    (l:ls)  -> (litComp l) `elem` ll || terminoTrue ls
--
--Tests:
--terminoTrue [Var 1, Neg $ Var 1] True elemento de CNF
--terminoTrue [Var 1, Neg $ Var 2] False elemento de DNF
--

termListTrue :: [[PL]] -> Bool
--Determina si alguna de los terminos (listas de literales) de una lista lc son false.
termListTrue ld = case ld of
                    []      -> True
                    (d:cc)  -> clausulaTrue d  ||  clauListTrue cc
--Tests:
--termListTrue [[Var 1, Neg $ Var 1], [Var 1, Neg $ Var 2]]
--
decideDNFenVAL :: PL -> Bool
--Decide si una formula-DNF pertenece, o no, a VAL:={phi in PL | forall m: m |= phi}
--Se aplica el algoritmo visto en clase.
--Ideas basicas:
--      Para revisar terminos y literales, phi se transforma en una lista de listas de literales.
--      Un termino (lista de literales) C no es valida sii C tiene un par de literales complementarios.
--      phi en DNF es valida sii todas las clausulas de phi no son validas.
decideDNFenVAL phi = termListTrue (dnf2LListLit phi)
--
--Tests en ghci:
--showDNF g15
--decideDNFenVAL g15
--inSAT g15
--inSAT (Neg g15)
--
--showDNF g16
--decideDNFenVAL g16
--inSAT g16
--inSAT (Neg g16)
--
