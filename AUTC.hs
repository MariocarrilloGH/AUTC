------------------------------------------------
--Funciones auxiliares--
------------------------------------------------

busqueda :: Eq a => a -> [a] -> Bool --Dado un elemento y una lista, devuelve si el elemento este en la lista--
busqueda _ [] = False
busqueda n (x:xs) = n==x || busqueda n xs

eliminar_repetidos :: (Eq a) => [a] -> [a] --Dada una lista, devuelve la lista sin elementos repetidos--
eliminar_repetidos [] = []
eliminar_repetidos (x:xs) = x : eliminar_repetidos (filter (/=x) xs)

eliminar_lista :: Eq a => a -> [a] -> [a] --Dado un elemento y una lista, devuelve la lista sin ese elemento (borra solo una aparición)--
eliminar_lista _ [] = []
eliminar_lista n (x:xs)
    |n==x = xs
    |otherwise = x:(eliminar_lista n xs)
    
combinaciones :: (String -> Bool) -> (String -> Bool) -> String -> String -> Bool --Dadas dos funciones de String en Bool y dos String, devuelve si hay alguna forma de separar la concatenación de las dos cadenas de manera que las dos funciones devuelvan True--
combinaciones f1 f2 acum [] = f1 acum && f2 []
combinaciones f1 f2 acum (x:xs) = (f1 acum && f2 (x:xs)) || combinaciones f1 f2 (acum++[x]) xs

prod_cart_listas :: [a] -> [b] -> [(a,b)] --Dadas dos listas, devuelve una lista con su producto cartesiano--
prod_cart_listas (x1:x1s) (x2:x2s) = (x1,x2):((prod_cart_listas (x1:x1s) x2s)++(prod_cart_listas x1s (x2:x2s)))
prod_cart_listas _ _ = []

igualesListas_sinOrden :: Eq a => [a] -> [a] -> Bool --Dadas dos listas, devuelve si tienen los mismos elementos--
igualesListas_sinOrden [] [] = True
igualesListas_sinOrden [] _ = False
igualesListas_sinOrden (x:xs) ys = (busqueda x ys) && (igualesListas_sinOrden xs (eliminar_lista x ys))

flip23 :: (a -> b -> c -> d) -> a -> c -> b -> d --Dada una función, devuelve de 3 parametros de entrada cambia el orden del 2 y el 3--
flip23 f x y z = f x z y

ordenar_lista :: Ord a => [a] -> [a] --Dada una lista de elementos ordenables te la devuelve ordenada de menor a mayor--
ordenar_lista [] = []
ordenar_lista (x:xs) = ordenar_lista menores ++ [x] ++ ordenar_lista mayores
  where (menores,mayores) = separa x xs
        separa x [] = ([],[])
        separa x (y:ys)
          | x < y     = (men,y:mas)
          | otherwise = (y:men,mas)
          where (men,mas) = separa x ys
          
posicion_lista :: Eq a => [a] -> a -> Int --Dada una lista y un elemento de la lista, devuelve el indice de su primera aparición en la lista (si se introduce algo indebido devuelve -1)--
posicion_lista [] _ = -1
posicion_lista (x:xs) y
    |x==y = 0
    |otherwise = (posicion_lista xs y) + 1

------------------------------------------------
--Conjuntos--
------------------------------------------------

data Cjto a = Cj [a]
    deriving (Read, Show)
instance Eq a => Eq (Cjto a) where
        Cj xs == Cj ys = igualesListas_sinOrden xs ys 

vacio_conj :: Eq a => Cjto a --Devuelve el conjunto vacio--
vacio_conj = Cj []

añadir_elem :: Eq a => a -> Cjto a -> Cjto a --Dado un elemento y un conjunto, devuelve el conjunto añadiendole el elemento--
añadir_elem n (Cj x)
    |busqueda n x = Cj x
    |otherwise = Cj (n:x)
    
es_conj_vacio :: Eq a => Cjto a -> Bool --Dado un conjunto, devuelve si es el conjunto vacio--
es_conj_vacio (Cj []) = True
es_conj_vacio _ = False

eliminar_elem :: Eq a => a -> Cjto a -> Cjto a --Dado un elemento y un conjunto, devuelve el conjunto sin el elemento--
eliminar_elem n (Cj x) = conj_lista (eliminar_lista n x)

busqueda_conj :: Eq a => a -> Cjto a -> Bool --Dado un elemento y un conjunto, devuelve si el elemento esta en el conjunto--
busqueda_conj n (Cj x) = busqueda n x

lista_conj :: Eq a => Cjto a -> [a] --Dado un conjunto, devuelve una lista con sus elementos--
lista_conj (Cj x) = x

cardinal :: Eq a => Cjto a -> Int --Dado un conjunto, devuelve su cardinal--
cardinal (Cj []) = 0
cardinal (Cj (x:xs)) = 1+cardinal (Cj xs)

producto_cartesiano :: (Eq a, Eq b) => Cjto a -> Cjto b -> Cjto (a,b) --Dados dos conjuntos, devuelve el conjunto de su producto cartesiano--
producto_cartesiano (Cj l1) (Cj l2) = conj_lista (prod_cart_listas l1 l2)

union :: Eq a => Cjto a -> Cjto a -> Cjto a --Dados dos conjuntos, devuelve el conjunto unión--
union c1 (Cj []) = c1
union c1 (Cj (x:xs)) = añadir_elem x (union c1 (Cj xs))

union_multiple :: Eq a => Cjto (Cjto a) -> Cjto a --Dado un conjunto de conjuntos, devuelve la unión de todos sus elementos--
union_multiple c = foldr_conj union (Cj []) c

menos_conj :: Eq a => Cjto a -> Cjto a -> Cjto a --Dados dos conjuntos A y B, devuelve A\B
menos_conj c (Cj []) = c
menos_conj c (Cj (x:xs)) = menos_conj (eliminar_elem x c) (Cj xs)

interseccion :: Eq a => Cjto a -> Cjto a -> Cjto a --Dados dos conjuntos, devuelve el conjunto intersección--
interseccion _ (Cj []) = Cj []
interseccion c1 (Cj (x:xs))
    |busqueda_conj x c1 = añadir_elem x (interseccion c1 (Cj xs))
    |otherwise = interseccion c1 (Cj xs)
    
potencia :: Eq a => Cjto a -> Cjto (Cjto a) --Dado un conjunto, devuelve el conjunto de sus subconjuntos--
potencia (Cj []) = Cj [Cj []]
potencia (Cj (x:xs)) = union sin_x con_x
    where 
        sin_x = potencia (Cj xs)
        con_x = map_conj (union (Cj [x])) sin_x

conj_lista :: Eq a => [a] -> Cjto a --Dada una lista, devuelve el conjunto con sus elementos (eliminando repeticiones)--
conj_lista [] = Cj []
conj_lista (x:xs) = añadir_elem x (conj_lista xs)

map_conj :: (Eq a, Eq b) => (a -> b) -> Cjto a -> Cjto b --Función map para conjuntos--
map_conj _ (Cj []) = Cj []
map_conj f (Cj (x:xs)) = añadir_elem (f x) (map_conj f (Cj xs))

foldr_conj :: Eq a => (a -> b -> b) -> b -> Cjto a -> b --Función foldr para conjuntos--
foldr_conj f e (Cj xs) = foldr f e xs

filter_conj :: Eq a => (a -> Bool) -> Cjto a -> Cjto a --Función filter para conjuntos--
filter_conj f (Cj []) = Cj []
filter_conj f (Cj (x:xs)) 
    |f x = añadir_elem x (filter_conj f (Cj xs))
    |otherwise = filter_conj f (Cj xs)

show_ordenado :: (Eq a, Ord a, Show a) => Cjto a -> String --Dado un conjunto de elementos ordenables, te lo devuelve en tipo String con los elementos ordenados--
show_ordenado (Cj xs) = show (Cj xs_ordenada)
    where xs_ordenada = ordenar_lista xs
    
proyeccion2 :: (Eq a, Eq b) => Cjto (a,b) -> Cjto b --Dado un conjunto de la forma AxB, devuelve B (la segunda proyección)--
proyeccion2 (Cj []) = Cj []
proyeccion2 (Cj ((x1,x2):xs)) = union (Cj [x2]) (proyeccion2 (Cj xs))

------------------------------------------------
--Expresiones regulares--
------------------------------------------------

data ER = Simbolo Char | Epsilon | Vacio | Parentesis ER | Suma ER ER | Producto ER ER | Estrella ER
    deriving (Show, Read, Eq)

epsilon_ER :: ER --Devuelve la ER (Epsilon)--
epsilon_ER = Epsilon

vacio_ER :: ER --Devuelve la ER (Vacio)--
vacio_ER = Vacio

char_ER :: Char -> ER --Dado un Char a, devuelve la ER a--
char_ER x = Simbolo x

parentesis_ER :: ER -> ER --Dada una ER E, devuelve (E)--
parentesis_ER e = Parentesis e

suma_ERs :: ER -> ER -> ER --Dadas dos ERs E y F, devuelve E+F--
suma_ERs e1 e2 = Suma e1 e2

producto_ERs :: ER -> ER -> ER --Dadas dos ERs E y F, devuelve EF--
producto_ERs e1 e2 = Producto e1 e2

estrella_ER :: ER -> ER --Dada una ER E, devuelve E*--
estrella_ER e = Estrella e

cadena_en_ER :: ER -> String -> Bool --Dada una ER E y una cadena w, devuelve si w pertenece a L(E)--
cadena_en_ER Vacio _ = False
cadena_en_ER Epsilon [] = True
cadena_en_ER Epsilon _ = False
cadena_en_ER (Simbolo x) c
    |c==(x:[]) = True
    |otherwise = False
cadena_en_ER (Parentesis e) x = cadena_en_ER e x
cadena_en_ER (Suma e1 e2) x = cadena_en_ER e1 x || cadena_en_ER e2 x
cadena_en_ER (Producto e1 e2) x = combinaciones (cadena_en_ER e1) (cadena_en_ER e2) [] x
cadena_en_ER (Estrella e) x = cadena_en_estrella_aux (length x) e e x
    where
        cadena_en_estrella_aux :: Int -> ER -> ER -> String -> Bool
        cadena_en_estrella_aux 0 _ _ x = x==[]
        cadena_en_estrella_aux n e0 e x = cadena_en_ER e x || cadena_en_estrella_aux (n-1) e0 (Producto e0 e) x

------------------------------------------------
--Autómatas finitos deterministas--
------------------------------------------------

type Estado = String
type Simbolo = Char
type Delta_AFD = Cjto ((Estado, Simbolo), Estado)
type Estados = Cjto Estado
type Simbolos = Cjto Simbolo
type AFD = (Estados, Simbolos, Delta_AFD, Estado, Estados) 

construir_AFD :: [Estado] -> [Simbolo] -> [((Estado, Simbolo), Estado)] -> Estado -> [Estado] -> AFD --Construye un AFD--
construir_AFD q sigma delta q0 f = (conj_lista q, conj_lista sigma, conj_lista delta, q0, conj_lista f)

eval_AFD :: AFD -> Estado -> Simbolo -> Estado --Dado un AFD A, un estado q y un simbolo a, devuelve el conjunto de estados a los que se llega en A con a partiendo de q--
eval_AFD afd estado simbolo = snd (takeFirst en_dominio delta_lista)
    where
        takeFirst f (x:xs)
            |f x = x
            |otherwise = takeFirst f xs
        en_dominio t
            |(fst t == (estado,simbolo)) = True
            |otherwise = False
        delta_lista = lista_conj (delta_AFD afd)

estados_AFD :: AFD -> Estados --Dado un AFD, devuelve su conjunto de estados--
estados_AFD (q, sigma, delta, q0, f) = q

simbolos_AFD :: AFD -> Simbolos --Dado un AFD, devuelve su conjunto de simbolos--
simbolos_AFD (q, sigma, delta, q0, f) = sigma

delta_AFD :: AFD -> Delta_AFD --Dado un AFD, devuelve su función delta--
delta_AFD (q, sigma, delta, q0, f) = delta

inicial_AFD :: AFD -> Estado --Dado un AFD, devuelve su estado inicial--
inicial_AFD (q, sigma, delta, q0, f) = q0 

finales_AFD :: AFD -> Estados --Dado un AFD, devuelve su conjunto de estados finales--
finales_AFD (q, sigma, delta, q0, f) = f

simbolos_de_p_a_q :: AFD -> Estado -> Estado -> Simbolos --Dado un AFD y dos estados p y q, devuelve el conjunto de simbolos tales que delta(p,simbolo)=q--
simbolos_de_p_a_q afd p q = map_conj snd (filter_conj (a_q afd) (producto_cartesiano (Cj [p]) (simbolos_AFD afd)))
    where
        a_q :: AFD -> (Estado, Simbolo) -> Bool
        a_q afd (p,a) = (eval_AFD afd p a) == q

delta_gorro_AFD :: AFD -> Estado -> [Simbolo] -> Estado --Dado un AFD A, un estado q y una cadena w, devuelve el conjunto de estados a los que se llega en A con w partiendo de q--
delta_gorro_AFD afd q [] = q
delta_gorro_AFD afd q w = eval_AFD afd (delta_gorro_AFD afd q x) a
    where
        x = init w
        a = last w

cadena_en_AFD :: AFD -> [Simbolo] -> Bool --Dado un AFD A y una cadena w, devuelve si w pertenece a L(A)--
cadena_en_AFD afd w = busqueda_conj (delta_gorro_AFD afd inicial w) finales
    where 
        inicial = inicial_AFD afd
        finales = finales_AFD afd

------------------------------------------------
--Autómatas finitos no deterministas--
------------------------------------------------

type Delta_AFN = Cjto ((Estado, Simbolo), Estados)
type AFN = (Estados, Simbolos, Delta_AFN, Estado, Estados)

construir_AFN :: [Estado] -> [Simbolo] -> [((Estado, Simbolo), Estados)] -> Estado -> [Estado] -> AFN --Construye un AFN--
construir_AFN q sigma delta q0 f = (conj_lista q, conj_lista sigma, conj_lista delta, q0, conj_lista f)

eval_AFN :: AFN -> Estado -> Simbolo -> Estados --Dado un AFN A, un estado q y un simbolo a, devuelve el conjunto de estados a los que se llega en A con a partiendo de q--
eval_AFN afn estado simbolo = snd (takeFirst en_dominio delta_lista)
    where
        takeFirst f (x:xs)
            |f x = x
            |otherwise = takeFirst f xs
        en_dominio t
            |(fst t == (estado,simbolo)) = True
            |otherwise = False
        delta_lista = lista_conj (delta_AFN afn)

estados_AFN :: AFN -> Estados --Dado un AFN, devuelve su conjunto de estados--
estados_AFN (q, sigma, delta, q0, f) = q

simbolos_AFN :: AFN -> Simbolos --Dado un AFN, devuelve su conjunto de simbolos--
simbolos_AFN (q, sigma, delta, q0, f) = sigma

delta_AFN :: AFN -> Delta_AFN --Dado un AFN, devuelve su función delta--
delta_AFN (q, sigma, delta, q0, f) = delta

inicial_AFN :: AFN -> Estado --Dado un AFN, devuelve su estado inicial--
inicial_AFN (q, sigma, delta, q0, f) = q0

finales_AFN :: AFN -> Estados --Dado un AFN, devuelve su conjunto de estados finales--
finales_AFN (q, sigma, delta, q0, f) = f

delta_gorro_AFN :: AFN -> Estado -> [Simbolo] -> Estados --Dado un AFN A, un estado q y una cadena w, devuelve el conjunto de estados a los que se llega en A con w partiendo de q--
delta_gorro_AFN afn q [] = Cj [q]
delta_gorro_AFN afn q w = union_multiple (map_conj ((flip23 eval_AFN) afn a) p_is)
    where
        x = init w
        a = last w
        p_is = delta_gorro_AFN afn q x

cadena_en_AFN :: AFN -> [Simbolo] -> Bool --Dado un AFN A y una cadena w, devuelve si w pertenece a L(A)--
cadena_en_AFN afn w = (interseccion (delta_gorro_AFN afn inicial w) finales) /= Cj []
    where 
        inicial = inicial_AFN afn
        finales = finales_AFN afn

---------------------------------------------------------------------
--Autómatas finitos no deterministas con transiciones epsilon--
---------------------------------------------------------------------

--Voy a utilizar la construcción del AFN para los AFN epsilon reservando el simbolo 'e' para epsilon--

type AFNe = AFN

clausura_epsilon :: AFNe -> Estado -> Estados --Dado un AFNe y un estado , devuelve su clausura_epsilon--
clausura_epsilon afne q = union (Cj [q]) (union_multiple (map_conj (clausura_epsilon afne) estados_q_e))
    where estados_q_e = menos_conj (delta_gorro_AFN afne q "e") (Cj [q])
    
delta_gorro_AFNe :: AFNe -> Estado -> [Simbolo] -> Estados --Dado un AFNe A, un estado q y una cadena w, devuelve el conjunto de estados a los que se llega en A con w partiendo de q--
delta_gorro_AFNe afne q [] = clausura_epsilon afne q
delta_gorro_AFNe afne q w = union_multiple (map_conj (clausura_epsilon afne) r_js)
    where 
        x = init w
        a = last w
        p_is = delta_gorro_AFNe afne q x
        r_js = union_multiple (map_conj ((flip23 eval_AFN) afne a) p_is) 

cadena_en_AFNe :: AFNe -> [Simbolo] -> Bool --Dado un AFNe A y una cadena w, devuelve si w pertenece a L(A)--
cadena_en_AFNe afne w = (interseccion (delta_gorro_AFNe afne inicial w) finales) /= Cj []
    where 
        inicial = inicial_AFN afne
        finales = finales_AFN afne
        
anadir_transiciones :: AFNe -> Delta_AFN -> Delta_AFN --Dado un AFNe A y un conjunto nuevo de transiciones las añade a las que ya tenemos--
anadir_transiciones afne nueva_delta = map_conj (snd_union nueva_delta) delta
    where
        delta = delta_AFN afne
        snd_union :: Delta_AFN -> ((Estado,Simbolo),Estados) -> ((Estado,Simbolo),Estados)
        snd_union (Cj []) t = t
        snd_union (Cj (((p1,a1),c1):xs)) ((p2,a2),c2)
            |(p1,a1)==(p2,a2) = ((p1,a1),union c1 c2)
            |otherwise = ((p2,a2),c2)
        
----------------------------------------------
--Algunos algoritmos y las conversiones--
----------------------------------------------

de_AFN_a_AFD :: AFN -> AFD --Dado un AFN A, devuelve un AFD A' con L(A)=L(A')--
de_AFN_a_AFD afn = construir_AFD (lista_conj (a_String q)) (lista_conj sigma) (lista_conj delta) q0 (lista_conj f)
    where
        q = potencia (estados_AFN afn)
        sigma = simbolos_AFN afn
        delta = map_conj delta_aux dominio_delta
        dominio_delta = producto_cartesiano q (simbolos_AFN afn)
        delta_aux (s,a) = ((show_ordenado s,a), show_ordenado (union_multiple (map_conj ((flip23 eval_AFN) afn a) s)))
        q0 = show_ordenado (Cj [(inicial_AFN afn)])
        f = a_String (filter_conj (interseccion_f_afn_no_vacio) q)
        interseccion_f_afn_no_vacio s = (interseccion s (finales_AFN afn)) /= Cj []
        a_String = map_conj show_ordenado 
        
de_AFNe_a_AFD :: AFNe -> AFD --Dado un AFNe A, devuelve un AFD A' con L(A)=L(A')--
de_AFNe_a_AFD afne = construir_AFD (lista_conj (a_String q)) (lista_conj sigma) (lista_conj delta) q0 (lista_conj f)
    where
        sigma = simbolos_AFN afne
        q = potencia (estados_AFN afne)
        delta = map_conj delta_aux dominio_delta
        dominio_delta = producto_cartesiano q (simbolos_AFN afne)
        delta_aux (s,a) = ((show_ordenado s,a), show_ordenado (union_multiple (map_conj (clausura_epsilon afne) r_js)))
            where r_js = union_multiple (map_conj ((flip23 eval_AFN) afne a) s)
        q0 = show_ordenado (clausura_epsilon afne (inicial_AFN afne))
        f = a_String (filter_conj (interseccion_f_afne_no_vacio) q)
        interseccion_f_afne_no_vacio s = (interseccion s (finales_AFN afne)) /= Cj []
        a_String = map_conj show_ordenado

de_AFD_a_AFN :: AFD -> AFN --Dado un AFD A, devuelve un AFN A' con L(A)=L(A')--
de_AFD_a_AFN afd = construir_AFN (lista_conj q) (lista_conj sigma) (lista_conj delta) q0 (lista_conj f)
    where
        q = estados_AFD afd
        sigma = simbolos_AFD afd
        q0 = inicial_AFD afd
        f = finales_AFD afd
        delta = map_conj a_conjunto (delta_AFD afd)
        a_conjunto (f,s) = (f,Cj [s])

de_AFD_a_AFNe :: AFD -> AFNe --Dado un AFD A, devuelve un AFNe A' con L(A)=L(A')--
de_AFD_a_AFNe afd = construir_AFN (lista_conj q) (lista_conj sigma) (lista_conj delta) q0 (lista_conj f)
    where
        q = estados_AFD afd
        sigma = union (simbolos_AFD afd) (Cj ['e'])
        q0 = inicial_AFD afd
        f = finales_AFD afd
        delta = union (map_conj a_conjunto (delta_AFD afd)) (producto_cartesiano dominio_delta_e (Cj [(Cj [])]))
        dominio_delta_e = producto_cartesiano q (Cj ['e'])
        a_conjunto (f,s) = (f,Cj [s])
        
de_AFD_a_ER :: AFD -> ER --Dado un AFD A, devuelve una ER E con L(A)=L(E)--
de_AFD_a_ER afd = suma_multiple (map_conj (r_kij afd n 1) finales)
    where
        a_numero :: AFD -> Estado -> Int
        a_numero afd p 
            |p==(inicial_AFD afd) = 1
            |otherwise = (posicion_lista (lista_conj (menos_conj (estados_AFD afd) (Cj [inicial_AFD afd]))) p) + 2
        a_estado :: AFD -> Int -> Estado
        a_estado afd 1 = inicial_AFD afd
        a_estado afd m = (lista_conj (menos_conj (estados_AFD afd) (Cj [inicial_AFD afd])))!!(m-2)
        n = cardinal (estados_AFD afd)
        finales =  map_conj (a_numero afd) (finales_AFD afd)
        suma_multiple :: Cjto ER -> ER
        suma_multiple (Cj []) = Vacio
        suma_multiple (Cj (e:xs)) = Suma e (suma_multiple (Cj xs))
        arcos :: Int -> Int -> Simbolos
        arcos i j = simbolos_de_p_a_q afd (a_estado afd i) (a_estado afd j)
        r_kij :: AFD -> Int -> Int -> Int -> ER
        r_kij afd 0 i j
            |i/=j = suma_multiple (map_conj char_ER (arcos i j))
            |otherwise = Suma Epsilon (suma_multiple (map_conj char_ER (arcos i j)))
        r_kij afd k i j = Suma (r_kij afd (k-1) i j) (Producto (r_kij afd (k-1) i k) (Producto (Estrella (r_kij afd (k-1) k k)) (r_kij afd (k-1) k j)))

de_ER_a_AFNe :: ER -> AFNe --Dada una ER E, devuelve un AFNe A con L(E)=L(A)--
de_ER_a_AFNe e = fst (de_ER_a_AFNe_aux e 0)

de_ER_a_AFNe_aux :: ER -> Int -> (AFNe,Int) --Función auxiliar para poder dar nombres diferentes a los estados del AFNe cuando pasamos de ER a AFNe--
de_ER_a_AFNe_aux Epsilon n = (construir_AFN [q0,q1] ['e'] [((q0,'e'),Cj [q1]), ((q1,'e'),Cj [])] q0 [q1], n+2)
    where
        q0 = "q"++show n
        q1 = "q"++show (n+1)
de_ER_a_AFNe_aux Vacio n = (construir_AFN [q0,q1] ['e'] [((q0,'e'),Cj []), ((q1,'e'),Cj [])] q0 [q1], n+2)
    where
        q0 = "q"++show n
        q1 = "q"++show (n+1)
de_ER_a_AFNe_aux (Simbolo c) n = (construir_AFN [q0,q1] ['e',c] [((q0,c),Cj [q1]), ((q0,'e'),Cj []), ((q1,c),Cj []), ((q1,'e'),Cj [])] q0 [q1], n+2)
    where
        q0 = "q"++show n
        q1 = "q"++show (n+1)
de_ER_a_AFNe_aux (Parentesis e) n = de_ER_a_AFNe_aux e n
de_ER_a_AFNe_aux (Estrella e) n = (construir_AFN estados (lista_conj simbolos) (lista_conj delta) inicial finales, n_e+2)
    where
        (afne_e, n_e) = de_ER_a_AFNe_aux e n
        estados = lista_conj (union (Cj [inicial, final]) (estados_AFN afne_e))
        simbolos = simbolos_AFN afne_e
        inicial = "q"++show n_e
        final = "q"++show (n_e+1)
        finales = [final]
        iniciale = inicial_AFN afne_e
        finalese_a_iniciale_y_final = producto_cartesiano (producto_cartesiano (finales_AFN afne_e) (Cj ['e'])) (Cj [Cj [iniciale,final]])
        transiciones_extra_final = producto_cartesiano (producto_cartesiano (Cj [final]) (simbolos)) (Cj [Cj []])
        transiciones_extra_inicial = producto_cartesiano (producto_cartesiano (Cj [inicial]) (menos_conj simbolos (Cj ['e']))) (Cj [Cj []])
        deltae = anadir_transiciones afne_e finalese_a_iniciale_y_final
        delta = union_multiple (Cj [deltae, transiciones_extra_inicial, transiciones_extra_final, Cj [((inicial,'e'),Cj [iniciale,final])]])
de_ER_a_AFNe_aux (Producto e1 e2) n = (construir_AFN estados simbolos (lista_conj delta) inicial finales, n_1+n_2+1)
    where 
        (afne_e1, n_1) = de_ER_a_AFNe_aux e1 n
        (afne_e2, n_2) = de_ER_a_AFNe_aux e2 (n+n_1)
        estados = lista_conj (union (estados_AFN afne_e1) (estados_AFN afne_e2))
        simbolos_1 = simbolos_AFN afne_e1
        simbolos_2 = simbolos_AFN afne_e2
        simbolos = lista_conj (union simbolos_1 simbolos_2)
        inicial = inicial_AFN afne_e1
        finales = lista_conj (finales_AFN afne_e2)
        finales1_a_inicial2 = producto_cartesiano (producto_cartesiano (finales_AFN afne_e1) (Cj ['e'])) (Cj [Cj [inicial_AFN afne_e2]])
        simbolos2_en_1 = producto_cartesiano (producto_cartesiano (estados_AFN afne_e1) (menos_conj simbolos_2 simbolos_1)) (Cj [Cj []])
        simbolos1_en_2 = producto_cartesiano (producto_cartesiano (estados_AFN afne_e2) (menos_conj simbolos_1 simbolos_2)) (Cj [Cj []])
        delta1 = anadir_transiciones afne_e1 finales1_a_inicial2
        delta = union_multiple (Cj [delta1, (delta_AFN afne_e2), simbolos2_en_1, simbolos1_en_2])
de_ER_a_AFNe_aux (Suma e1 e2) n = (construir_AFN estados (lista_conj simbolos) (lista_conj delta) inicial finales, n_1+n_2+2)
    where 
        (afne_e1, n_1) = de_ER_a_AFNe_aux e1 n
        (afne_e2, n_2) = de_ER_a_AFNe_aux e2 (n+n_1)
        estados = lista_conj (union_multiple (Cj [Cj [inicial, final], (estados_AFN afne_e1), (estados_AFN afne_e2)]))
        simbolos_1 = simbolos_AFN afne_e1
        simbolos_2 = simbolos_AFN afne_e2
        simbolos = union simbolos_1 simbolos_2
        inicial = "q"++show (n_1+n_2)
        final = "q"++show (n_1+n_2+1)
        finales = [final]
        inicial_a_iniciales = producto_cartesiano (producto_cartesiano (Cj [inicial]) (Cj ['e'])) (Cj [Cj [inicial_AFN afne_e1, inicial_AFN afne_e2]])
        finales1_a_final = producto_cartesiano (producto_cartesiano (finales_AFN afne_e1) (Cj ['e'])) (Cj [Cj [final]])
        finales2_a_final = producto_cartesiano (producto_cartesiano (finales_AFN afne_e2) (Cj ['e'])) (Cj [Cj [final]])
        simbolos2_en_1 = producto_cartesiano (producto_cartesiano (estados_AFN afne_e1) (menos_conj simbolos_2 simbolos_1)) (Cj [Cj []])
        simbolos1_en_2 = producto_cartesiano (producto_cartesiano (estados_AFN afne_e2) (menos_conj simbolos_1 simbolos_2)) (Cj [Cj []])
        delta1 = anadir_transiciones afne_e1 finales1_a_final
        delta2 = anadir_transiciones afne_e2 finales2_a_final
        transiciones_extra_final = producto_cartesiano (producto_cartesiano (Cj [final]) simbolos) (Cj [Cj []])
        transiciones_extra_inicial = producto_cartesiano (producto_cartesiano (Cj [inicial]) (menos_conj simbolos (Cj ['e']))) (Cj [Cj []])
        delta = union_multiple (Cj [delta1, delta2, inicial_a_iniciales, transiciones_extra_inicial, transiciones_extra_final, simbolos2_en_1, simbolos1_en_2])

de_AFN_a_AFNe :: AFN -> AFNe --Dado un AFN A, devuelve un AFNe A' con L(A)=L(A')--
de_AFN_a_AFNe = de_AFD_a_AFNe . de_AFN_a_AFD

de_AFN_a_ER :: AFN -> ER --Dado un AFN A, devuelve una ER E con L(A)=L(E)--
de_AFN_a_ER = de_AFD_a_ER . de_AFN_a_AFD

de_AFNe_a_AFN :: AFNe -> AFN --Dado un AFNe A, devuelve un AFN A' con L(A)=L(A')--
de_AFNe_a_AFN = de_AFD_a_AFN . de_AFNe_a_AFD

de_AFNe_a_ER :: AFNe -> ER --Dado un AFNe A, devuelve una ER E con L(A)=L(E)--
de_AFNe_a_ER = de_AFD_a_ER . de_AFNe_a_AFD

de_ER_a_AFD :: ER -> AFD --Dada una ER E, devuelve un AFD A con L(E)=L(A)--
de_ER_a_AFD = de_AFNe_a_AFD . de_ER_a_AFNe

de_ER_a_AFN :: ER -> AFN --Dada una ER E, devuelve un AFN A con L(E)=L(A)--
de_ER_a_AFN = de_AFD_a_AFN . de_AFNe_a_AFD . de_ER_a_AFNe

es_vacio_L :: ER -> Bool --Dada una ER E, devuelve si L(E)={}--
es_vacio_L Epsilon = False
es_vacio_L Vacio = True
es_vacio_L (Simbolo _) = False
es_vacio_L (Suma e1 e2) = (es_vacio_L e1) && (es_vacio_L e2)
es_vacio_L (Producto e1 e2) = (es_vacio_L e1) || (es_vacio_L e2)
es_vacio_L (Estrella e) = False
es_vacio_L (Parentesis e) = es_vacio_L e

es_epsilon_L :: ER -> Bool --Dada una ER E, devuelve si L(E)={epsilon}--
es_epsilon_L Epsilon = True
es_epsilon_L Vacio = False
es_epsilon_L (Simbolo _) = False
es_epsilon_L (Suma e1 e2) = ((es_epsilon_L e1) && (es_epsilon_L e2)) || ((es_epsilon_L e1) && (es_vacio_L e2)) || ((es_epsilon_L e2) && (es_vacio_L e1))
es_epsilon_L (Producto e1 e2) = (es_epsilon_L e1) && (es_epsilon_L e2)
es_epsilon_L (Estrella e) = (es_vacio_L e) || (es_epsilon_L e)
es_epsilon_L (Parentesis e) = es_epsilon_L e

es_finito_L :: ER -> Bool --Dada una ER E, devuelve si L(E) es finito--
es_finito_L Epsilon = True
es_finito_L Vacio = True
es_finito_L (Simbolo _) = True
es_finito_L (Suma e1 e2) = (es_finito_L e1) && (es_finito_L e2)
es_finito_L (Producto e1 e2) = (es_vacio_L e1) || (es_vacio_L e2) || ((es_finito_L e1) && (es_finito_L e2))
es_finito_L (Estrella e) = (es_vacio_L e) || (es_epsilon_L e)
es_finito_L (Parentesis e) = es_finito_L e

es_infinito_L :: ER -> Bool --Dada una ER E, devuelve si L(E) es infinito--
es_infinito_L er = not (es_finito_L er)

resta_AFDs :: AFD -> AFD -> AFD --Dados dos AFDs A1 y A2, devuelve un AFD A con L(A)=L(A1)\L(A2)--
resta_AFDs afd1 afd2 = construir_AFD (lista_conj (a_String estados)) (lista_conj simbolos) (lista_conj delta) inicial (lista_conj (a_String finales))
    where
        a_String = map_conj show
        estados = producto_cartesiano (estados_AFD afd1) (estados_AFD afd2)
        simbolos = simbolos_AFD afd1
        inicial = show (inicial_AFD afd1,inicial_AFD afd2)
        finales = producto_cartesiano (finales_AFD afd1) (no_finales2)
        no_finales2 = menos_conj (estados_AFD afd2) (finales_AFD afd2)
        delta = map_conj delta_aux dominio_delta
        dominio_delta = producto_cartesiano estados simbolos
        delta_aux ((p,q),a) = ((show (p,q),a), show (eval_AFD afd1 p a,eval_AFD afd2 q a))

interseccion_AFDs :: AFD -> AFD -> AFD --Dados dos AFDs A1 y A2, devuelve un AFD A con L(A)=L(A1) unión L(A2)--
interseccion_AFDs afd1 afd2 = construir_AFD (lista_conj (a_String estados)) (lista_conj simbolos) (lista_conj delta) inicial (lista_conj (a_String finales))
    where
        a_String = map_conj show
        estados = producto_cartesiano (estados_AFD afd1) (estados_AFD afd2)
        simbolos = simbolos_AFD afd1
        inicial = show (inicial_AFD afd1,inicial_AFD afd2)
        finales = producto_cartesiano (finales_AFD afd1) (finales_AFD afd2)
        delta = map_conj delta_aux dominio_delta
        dominio_delta = producto_cartesiano estados simbolos
        delta_aux ((p,q),a) = ((show (p,q),a), show (eval_AFD afd1 p a,eval_AFD afd2 q a))
        

union_AFDs :: AFD -> AFD -> AFD --Dados dos AFDs A1 y A2, devuelve un AFD A con L(A)=L(A1) intersección L(A2)--
union_AFDs afd1 afd2 = construir_AFD (lista_conj (a_String estados)) (lista_conj simbolos) (lista_conj delta) inicial (lista_conj (a_String finales))
    where
        a_String = map_conj show
        estados = producto_cartesiano (estados_AFD afd1) (estados_AFD afd2)
        simbolos = simbolos_AFD afd1
        inicial = show (inicial_AFD afd1,inicial_AFD afd2)
        finales = menos_conj estados no_finales_union
        no_finales_union = producto_cartesiano no_finales1 no_finales2
        no_finales1 = menos_conj (estados_AFD afd1) (finales_AFD afd1)
        no_finales2 = menos_conj (estados_AFD afd2) (finales_AFD afd2)
        delta = map_conj delta_aux dominio_delta
        dominio_delta = producto_cartesiano estados simbolos
        delta_aux ((p,q),a) = ((show (p,q),a), show (eval_AFD afd1 p a,eval_AFD afd2 q a))

alguna_cadena_comun :: AFD -> AFD -> Bool --Dados dos AFDs A1 y A2, devuelve si L(A1) y L(A2) tienen alguna cadena en comun--
alguna_cadena_comun afd1 afd2 = not (es_vacio_L (de_AFD_a_ER (interseccion_AFDs afd1 afd2)))

es_el_total_L :: AFD -> Bool --Dado un AFD A, devuelve si L(A) es el lenguaje total--
es_el_total_L afd = es_vacio_L (de_AFD_a_ER (resta_AFDs afd_total afd))
    where 
        afd_total = construir_AFD ["q_acepta"] (lista_conj simbolos) (lista_conj delta) "q_acepta" ["q_acepta"]
        simbolos = simbolos_AFD afd
        delta = producto_cartesiano dominio_delta (Cj ["q_acepta"])
        dominio_delta = producto_cartesiano (Cj ["q_acepta"]) simbolos
        
aceptan_mismo_lenguaje :: AFD -> AFD -> Bool --Dados dos AFDs A1 y A2, devuelve si L(A1)=L(A2)--
aceptan_mismo_lenguaje afd1 afd2 = es_vacio_L (de_AFD_a_ER (resta_AFDs afd1 afd2))

---------------------------------------
--Menu--
---------------------------------------

leeCadena :: IO [Simbolo]
leeCadena = do s <- getLine
               let readS = read :: String -> [Simbolo]
               return (readS s)

leeInt :: IO Int
leeInt = do n <- getLine
            return (read n)

leeIntenRango :: Int -> Int -> IO Int
leeIntenRango men may = do putStr ("Introduce un número entre " ++ show men ++ " y " ++ show may ++ " : ")
                           n <- leeInt
                           if (n>=men) && (n<=may)
                                then return n
                                else do putStrLn "Fuera de rango, repite"
                                        leeIntenRango men may

leeAFD :: IO AFD
leeAFD = do a <- getLine
            let readAFD = read :: String -> AFD
            return (readAFD a)
            
leeAFN :: IO AFN
leeAFN = do a <- getLine
            let readAFN = read :: String -> AFN
            return (readAFN a)

leeAFNe :: IO AFNe
leeAFNe = do a <- getLine
             let readAFNe = read :: String -> AFNe
             return (readAFNe a)

leeER :: IO ER
leeER = do er <- getLine
           let readER = read :: String -> ER 
           return (readER er) 

leeMaquina :: IO String
leeMaquina = do putStrLn "Introduce 'AFD', 'AFN', 'AFNe' o 'ER': "
                m <- getLine
                if (m=="AFD" || m=="AFN" || m=="AFNe" || m=="ER")
                    then return m
                    else do putStrLn "Mal escrito, repite"
                            leeMaquina

opcion1 :: IO()
opcion1 = do maquina <- leeMaquina
             case maquina of 
                "AFD" -> opcion1AFD
                "AFN" -> opcion1AFN
                "AFNe" -> opcion1AFNe
                "ER" -> opcion1ER

opcion1AFD :: IO()
opcion1AFD = do putStrLn "Introduce el AFD: "
                afd <- leeAFD
                putStrLn "Introduce la cadena: "
                cadena <- leeCadena
                let solucion = (cadena_en_AFD afd cadena)
                print (solucion)
                
opcion1AFN :: IO()
opcion1AFN = do putStrLn "Introduce el AFN: "
                afn <- leeAFN
                putStrLn "Introduce la cadena: "
                cadena <- leeCadena
                let solucion = (cadena_en_AFN afn cadena)
                print (solucion)

opcion1AFNe :: IO()
opcion1AFNe = do putStrLn "Introduce el AFNe: "
                 afne <- leeAFNe
                 putStrLn "Introduce la cadena: "
                 cadena <- leeCadena
                 let solucion = (cadena_en_AFNe afne cadena)
                 print (solucion)
                 
opcion1ER :: IO()
opcion1ER = do putStrLn "Introduce la ER: "
               er <- leeER
               putStrLn "Introduce la cadena: "
               cadena <- leeCadena
               let solucion = (cadena_en_ER er cadena)
               print (solucion)
              
opcion2 :: IO()
opcion2 = do putStrLn "Introduce el tipo del que quieres convertir: "
             maquina <- leeMaquina
             case maquina of 
                "AFD" -> opcion2AFD
                "AFN" -> opcion2AFN
                "AFNe" -> opcion2AFNe
                "ER" -> opcion2ER

opcion2_aux :: String -> IO()
opcion2_aux solucion = do putStrLn "Introduce el nombre del fichero de salida: "
                          nombreOut <- getLine
                          writeFile nombreOut solucion

opcion2AFD :: IO()
opcion2AFD = do putStrLn "Introduce el nombre del fichero con el AFD: "
                nombreIn <- getLine
                contenido <- readFile nombreIn
                let readAFD = read :: String -> AFD
                    afd = readAFD contenido
                putStrLn "Introduce el tipo al que quieres convertir: "
                maquina2 <- leeMaquina
                case maquina2 of
                    "AFD" -> do let solucion = show afd
                                opcion2_aux solucion
                    "AFN" -> do let solucion = show (de_AFD_a_AFN afd)
                                opcion2_aux solucion
                    "AFNe" -> do let solucion = show (de_AFD_a_AFNe afd)
                                 opcion2_aux solucion
                    "ER" -> do let solucion = show (de_AFD_a_ER afd)
                               opcion2_aux solucion 
                    
opcion2AFN :: IO()
opcion2AFN = do putStrLn "Introduce el nombre del fichero con el AFN: "
                nombreIn <- getLine
                contenido <- readFile nombreIn
                let readAFN = read :: String -> AFN
                    afn = readAFN contenido
                putStrLn "Introduce el tipo al que quieres convertir: "
                maquina2 <- leeMaquina
                case maquina2 of
                    "AFD" -> do let solucion = show (de_AFN_a_AFD afn)
                                opcion2_aux solucion
                    "AFN" -> do let solucion = show afn
                                opcion2_aux solucion
                    "AFNe" -> do let solucion = show (de_AFN_a_AFNe afn)
                                 opcion2_aux solucion
                    "ER" -> do let solucion = show (de_AFN_a_ER afn)
                               opcion2_aux solucion

opcion2AFNe :: IO()
opcion2AFNe = do putStrLn "Introduce el nombre del fichero con el AFNe: "
                 nombreIn <- getLine
                 contenido <- readFile nombreIn
                 let readAFNe = read :: String -> AFNe
                     afne = readAFNe contenido
                 putStrLn "Introduce el tipo al que quieres convertir: "
                 maquina2 <- leeMaquina
                 case maquina2 of
                     "AFD" -> do let solucion = show (de_AFNe_a_AFD afne)
                                 opcion2_aux solucion
                     "AFN" -> do let solucion = show (de_AFNe_a_AFN afne)
                                 opcion2_aux solucion
                     "AFNe" -> do let solucion = show afne
                                  opcion2_aux solucion
                     "ER" -> do let solucion = show (de_AFNe_a_ER afne)
                                opcion2_aux solucion
                     
opcion2ER :: IO()
opcion2ER = do putStrLn "Introduce el nombre del fichero con la ER: "
               nombreIn <- getLine
               contenido <- readFile nombreIn
               let readER = read :: String -> ER
                   er = readER contenido
               putStrLn "Introduce el tipo al que quieres convertir: "
               maquina2 <- leeMaquina
               case maquina2 of
                   "AFD" -> do let solucion = show (de_ER_a_AFD er)
                               opcion2_aux solucion
                   "AFN" -> do let solucion = show (de_ER_a_AFN er)
                               opcion2_aux solucion
                   "AFNe" -> do let solucion = show (de_ER_a_AFNe er)
                                opcion2_aux solucion
                   "ER" -> do let solucion = show er
                              opcion2_aux solucion
                   
opcion3 :: IO()
opcion3 = do putStrLn "    1: Dados dos AFDs A1 y A2, ¿L(A1)=L(A2)?"
             putStrLn "    2: Dada una ER E, ¿L(E)={}?"
             putStrLn "    3: Dada una ER E, ¿L(E)={Epsilon}?"
             putStrLn "    4: Dada una ER E, ¿L(E) es finito?"
             putStrLn "    5: Dada una ER E, ¿L(E) es infinito?"
             putStrLn "    6: Dados dos AFDs A1 y A2, construye otro que acepta L(A1) salvo L(A2)"
             putStrLn "    7: Dados dos AFDs A1 y A2, construye otro que acepta L(A1) intersección L(A2)"
             putStrLn "    8: Dados dos AFDs A1 y A2, construye otro que acepta L(A1) unión L(A2)"
             putStrLn "    9: Dados dos AFDs A1 y A2, ¿L(A1) y L(A2) tienen alguna cadena en común?"
             putStrLn "    10: Dado un AFD A, ¿L(A) es el lenguaje total?"
             putStrLn "    11: Volver al menu"
             opcion <- leeIntenRango 1 12
             case opcion of
                 1 -> do opcion3_1
                         opcion3
                 2 -> do opcion3_2
                         opcion3
                 3 -> do opcion3_3
                         opcion3
                 4 -> do opcion3_4
                         opcion3
                 5 -> do opcion3_5
                         opcion3
                 6 -> do opcion3_6
                         opcion3
                 7 -> do opcion3_7
                         opcion3
                 8 -> do opcion3_8
                         opcion3
                 9 -> do opcion3_9
                         opcion3
                 10 -> do opcion3_10
                          opcion3
                 11 -> menu
               
opcion3_1 :: IO()
opcion3_1 = do putStrLn "Introduce la AFD A1: "
               afd1 <- leeAFD
               putStrLn "Introduce la AFD A2: "
               afd2 <- leeAFD
               print (aceptan_mismo_lenguaje afd1 afd2)

opcion3_2 :: IO()
opcion3_2 = do putStrLn "Introduce la ER: "
               er <- leeER
               print (es_vacio_L er)
               
opcion3_3 :: IO()
opcion3_3 = do putStrLn "Introduce la ER: "
               er <- leeER
               print (es_epsilon_L er)
               
opcion3_4 :: IO()
opcion3_4 = do putStrLn "Introduce la ER: "
               er <- leeER
               print (es_finito_L er)

opcion3_5 :: IO()
opcion3_5 = do putStrLn "Introduce la ER: "
               er <- leeER
               print (es_infinito_L er)
               
opcion3_6 :: IO()
opcion3_6 = do putStrLn "Introduce el AFD A1: "
               afd1 <- leeAFD
               putStrLn "Introduce el AFD A2: "
               afd2 <- leeAFD
               print (resta_AFDs afd1 afd2)
               
opcion3_7 :: IO()
opcion3_7 = do putStrLn "Introduce el AFD A1: "
               afd1 <- leeAFD
               putStrLn "Introduce el AFD A2: "
               afd2 <- leeAFD
               print (interseccion_AFDs afd1 afd2)

opcion3_8 :: IO()
opcion3_8 = do putStrLn "Introduce el AFD A1: "
               afd1 <- leeAFD
               putStrLn "Introduce el AFD A2: "
               afd2 <- leeAFD
               print (union_AFDs afd1 afd2)

opcion3_9 :: IO()
opcion3_9 = do putStrLn "Introduce el AFD A1: "
               afd1 <- leeAFD
               putStrLn "Introduce el AFD A2: "
               afd2 <- leeAFD
               print (alguna_cadena_comun afd1 afd2)

opcion3_10 :: IO()
opcion3_10 = do putStrLn "Introduce el AFD: "
                afd <- leeAFD
                print (es_el_total_L afd)               

menu :: IO()
menu = do putStrLn "1: Comprobar si una cadena esta en un autómata o en una expresión regular"
          putStrLn "2: Convertir entre tipos de autómatas o expresión regular desde ficheros"
          putStrLn "3: Algoritmos varios sobre autómatas y expresiones regulares"
          putStrLn "4: Terminar"
          opcion <- leeIntenRango 1 4
          case opcion of
            1 -> do opcion1
                    menu
            2 -> do opcion2
                    menu
            3 -> do opcion3
            4 -> putStrLn "Hasta luego"