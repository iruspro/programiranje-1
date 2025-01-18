(* ========== Vaje 11: Iskalna Drevesa  ========== *)

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
 Ocaml omogoča enostavno delo z drevesi. Konstruiramo nov tip dreves, ki so
 bodisi prazna, bodisi pa vsebujejo podatek in imajo dve (morda prazni)
 poddrevesi. Na tej točki ne predpostavljamo ničesar drugega o obliki dreves.
[*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)
type 'a tree =     
  | Empty
  | Node of ('a tree * 'a  * 'a tree)


(*----------------------------------------------------------------------------*]
 Definirajmo si testni primer za preizkušanje funkcij v nadaljevanju. Testni
 primer predstavlja spodaj narisano drevo, pomagamo pa si s pomožno funkcijo
 [leaf], ki iz podatka zgradi list.
          5
         / \
        2   7
       /   / \
      0   6   11
[*----------------------------------------------------------------------------*)
let leaf x = Node (Empty, x, Empty)
let test_tree = Node (Node (leaf 0, 2, Empty), 5, Node (leaf 6, 7, leaf 11))

(*----------------------------------------------------------------------------*]
 Funkcija [mirror] vrne prezrcaljeno drevo. Na primeru [test_tree] torej vrne
          5
         / \
        7   2
       / \   \
      11  6   0
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # mirror test_tree ;;
 - : int tree =
 Node (Node (Node (Empty, 11, Empty), 7, Node (Empty, 6, Empty)), 5,
 Node (Empty, 2, Node (Empty, 0, Empty)))
[*----------------------------------------------------------------------------*)
let rec mirror t =
  match t with
  | Empty -> Empty
  | Node (l, x, r) -> Node (mirror r, x, mirror l)

(*----------------------------------------------------------------------------*]
 Funkcija [height] vrne višino oz. globino drevesa, funkcija [size] pa število
 vseh vozlišč drevesa.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # height test_tree;;
 - : int = 3
 # size test_tree;;
 - : int = 6
[*----------------------------------------------------------------------------*)
let rec height t = 
  match t with
  | Empty -> 0
  | Node (l, x, r) -> 1 + max (height l) (height r)

let rec size t =
  match t with
  | Empty -> 0
  | Node (l, x, r) -> 1 + size l + size r

(*----------------------------------------------------------------------------*]
 Funkcija [map_tree f tree] preslika drevo v novo drevo, ki vsebuje podatke
 drevesa [tree] preslikane s funkcijo [f].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # map_tree ((<)3) test_tree;;
 - : bool tree =
 Node (Node (Node (Empty, false, Empty), false, Empty), true,
 Node (Node (Empty, true, Empty), true, Node (Empty, true, Empty)))
[*----------------------------------------------------------------------------*)
let rec map_tree f t = 
  match t with
  | Empty -> Empty
  | Node (l, x, r) -> Node (map_tree f l, f x, map_tree f r) 

(*----------------------------------------------------------------------------*]
 Funkcija [list_of_tree] pretvori drevo v seznam. Vrstni red podatkov v seznamu
 naj bo takšen, da v primeru binarnega iskalnega drevesa vrne urejen seznam.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # list_of_tree test_tree;;
 - : int list = [0; 2; 5; 6; 7; 11]
[*----------------------------------------------------------------------------*)
let rec list_of_tree t =
  match t with
  | Empty -> []
  | Node (l, x, r) -> (list_of_tree l) @ (x::list_of_tree r)

(*----------------------------------------------------------------------------*]
 Funkcija [is_bst] preveri ali je drevo binarno iskalno drevo (Binary Search 
 Tree, na kratko BST). Predpostavite, da v drevesu ni ponovitev elementov, 
 torej drevo npr. ni oblike Node( leaf 1, 1, leaf 2)). Prazno drevo je BST.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # is_bst test_tree;;
 - : bool = true
 # test_tree |> mirror |> is_bst;;
 - : bool = false
[*----------------------------------------------------------------------------*)
let rec is_bst t =
     let rec is_lower x t =
          match t with
          | Empty -> true
          | Node (l, y, r) -> 
               if y < x then
                    (is_lower x l) && (is_lower x r)
               else
                    false
     in
     let rec is_greater x t = 
          match t with
          | Empty -> true
          | Node (l, y, r) ->
               if y > x then
                    (is_greater x l) && (is_greater x r)
               else
                    false
     in
     match t with
     | Empty -> true
     | Node (l, x, r) -> (is_lower x l) && (is_greater x r) && (is_bst l) && (is_bst r)

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
 V nadaljevanju predpostavljamo, da imajo dvojiška drevesa strukturo BST.
[*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

(*----------------------------------------------------------------------------*]
 Funkcija [insert] v iskalno drevo pravilno vstavi dani element. Funkcija 
 [member] preveri ali je dani element v iskalnem drevesu.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # insert 2 (leaf 4);;
 - : int tree = Node (Node (Empty, 2, Empty), 4, Empty)
 # member 3 test_tree;;
 - : bool = false
[*----------------------------------------------------------------------------*)
let rec insert x t =
  match t with
  | Empty -> leaf x
  | Node (l, y, r) -> 
     if x < y then
       Node (insert x l, y, r)
     else
       Node (l, y, insert x r)

let rec member x t = 
     match t with
     | Empty -> false
     | Node (l, y, r) ->
          if x = y then
               true
          else if x < y then
               member x l
          else
               member x r

(*----------------------------------------------------------------------------*]
 Funkcija [member2] ne privzame, da je drevo bst.
 
 Opomba: Premislte kolikšna je časovna zahtevnost funkcije [member] in kolikšna
 funkcije [member2] na drevesu z n vozlišči, ki ima globino log(n). 
[*----------------------------------------------------------------------------*)
let rec member2 x t = 
     match t with
     | Empty -> false
     | Node (l, y, r) ->
          if y = x then
               true
          else
               (member x l) || (member x r)

(*----------------------------------------------------------------------------*]
 Funkcija [succ] vrne naslednjika korena danega drevesa, če obstaja. Za drevo
 oblike [bst = Node(l, x, r)] vrne najmanjši element drevesa [bst], ki je večji
 od korena [x].
 Funkcija [pred] simetrično vrne največji element drevesa, ki je manjši od
 korena, če obstaja.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # succ test_tree;;
 - : int option = Some 6
 # pred (Node(Empty, 5, leaf 7));;
 - : int option = None
[*----------------------------------------------------------------------------*)
let rec succ t =
     match t with
     | Empty -> None
     | Node (l, y, r) -> 
          match list_of_tree r with
          | [] -> None
          | x::xs -> Some x

let rec pred t = 
     match t with
     | Empty -> None
     | Node (l, y, r) ->
          match List.rev (list_of_tree l) with
          | [] -> None
          | x::xs -> Some x

(*----------------------------------------------------------------------------*]
 Na predavanjih ste omenili dva načina brisanja elementov iz drevesa. Prvi 
 uporablja [succ], drugi pa [pred]. Funkcija [delete x bst] iz drevesa [bst] 
 izbriše element [x], če ta v drevesu obstaja. Za vajo lahko implementirate
 oba načina brisanja elementov.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # (*<< Za [delete] definiran s funkcijo [succ]. >>*)
 # delete 7 test_tree;;
 - : int tree =
 Node (Node (Node (Empty, 0, Empty), 2, Empty), 5,
 Node (Node (Empty, 6, Empty), 11, Empty))
[*----------------------------------------------------------------------------*)
let rec delete x t = 
     if member x t then
          match t with
          | Empty -> Empty
          | Node (l, y, r) -> 
               if y = x then
                    match succ (Node (l, y, r)) with
                    | None -> l
                    | Some successor -> Node (l, successor, delete successor r)
               else
                    Node (delete x l, y, delete x r)
     else
          t

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
 SLOVARJI

 S pomočjo BST lahko (zadovoljivo) učinkovito definiramo slovarje. V praksi se
 slovarje definira s pomočjo hash tabel, ki so še učinkovitejše. V nadaljevanju
 pa predpostavimo, da so naši slovarji [dict] binarna iskalna drevesa, ki v
 vsakem vozlišču hranijo tako ključ kot tudi pripadajočo vrednost, in imajo BST
 strukturo glede na ključe. Ker slovar potrebuje parameter za tip ključa in tip
 vrednosti, ga parametriziramo kot [('key, 'value) dict].
[*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)
type ('key, 'value) dict =
  | Empty
  | Node of (('key, 'value) dict) * ('key * 'value) * (('key, 'value) dict)

(*----------------------------------------------------------------------------*]
 Napišite testni primer [test_dict]:
      "b":1
      /    \
  "a":0  "d":2
         /
     "c":-2
[*----------------------------------------------------------------------------*)
let test_dict = Node (Node (Empty, ("a", 0), Empty), ("b", 1), Node (Node (Empty, ("c", -2), Empty), ("d", 2), Empty))

(*----------------------------------------------------------------------------*]
 Funkcija [dict_get key dict] v slovarju poišče vrednost z ključem [key]. Ker
 slovar vrednosti morda ne vsebuje, vrne [option] tip.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # dict_get "banana" test_dict;;
 - : 'a option = None
 # dict_get "c" test_dict;;
 - : int option = Some (-2)
[*----------------------------------------------------------------------------*)
let rec dict_get key dict =
  match dict with
  | Empty -> None
  | Node (l, (k, v), r) -> 
      if key = k then
        Some v
      else if key < k then
        dict_get key l
      else 
        dict_get key r
      
(*----------------------------------------------------------------------------*]
 Funkcija [print_dict] sprejme slovar s ključi tipa [string] in vrednostmi tipa
 [int] in v pravilnem vrstnem redu izpiše vrstice "ključ : vrednost" za vsa
 vozlišča slovarja.
 Namig: Uporabite funkciji [print_string] in [print_int]. Nize združujemo z
 operatorjem [^]. V tipu funkcije si oglejte, kako uporaba teh funkcij določi
 parametra za tip ključev in vrednosti v primerjavi s tipom [dict_get].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # print_dict test_dict;;
 a : 0
 b : 1
 c : -2
 d : 2
 - : unit = ()
[*----------------------------------------------------------------------------*)
let rec print_dict dict =
  match dict with
  | Empty -> ()
  | Node (l, (k, v), r) ->
     print_dict l;
     print_string (k ^ " : ");
     print_int v;
     print_string "\n";
     print_dict r

(*----------------------------------------------------------------------------*]
 Funkcija [dict_insert key value dict] v slovar [dict] pod ključ [key] vstavi
 vrednost [value]. Če za nek ključ vrednost že obstaja, jo zamenja.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # dict_insert "1" 14 test_dict |> print_dict;;
 1 : 14
 a : 0
 b : 1
 c : -2
 d : 2
 - : unit = ()
 # dict_insert "c" 14 test_dict |> print_dict;;
 a : 0
 b : 1
 c : 14
 d : 2
 - : unit = ()
[*----------------------------------------------------------------------------*)
let rec dict_insert key value dict =
  match dict with
  | Empty -> Node (Empty, (key, value), Empty)
  | Node (l, (k, v), r) ->
      if k = key then
        Node (l, (k, value), r)
      else if key < k then
        Node (dict_insert key value l, (k, v), r)
      else
        Node (l, (k, v), dict_insert key value r)
(*----------------------------------------------------------------------------*]
 Napišite primerno signaturo za slovarje [DICT] in naredite implementacijo
 modula z drevesi. 
 
 Modul naj vsebuje prazen slovar [empty] in pa funkcije [get], [insert] in
 [print] (print naj ponovno deluje zgolj na [(string, int) t].
[*----------------------------------------------------------------------------*)
module type DICT =
  sig 
    type ('key, 'value) t 
    val empty : ('key, 'value) t 
    val get : 'key -> ('key, 'value) t -> 'value option
    val insert : 'key -> 'value -> ('key, 'value) t -> ('key, 'value) t
    val print : (string, int) t -> unit
  end

module Tree_dict : DICT = struct
     type ('key, 'value) t =
     | Empty
     | Node of (('key, 'value) t) * ('key * 'value) * (('key, 'value) t)
     let empty = Empty
     let rec get key dict = 
       match dict with
       | Empty -> None
       | Node (l, (k, v), r) -> 
           if key = k then
             Some v
           else if key < k then
               get key l
           else 
               get key r
     let rec insert key value dict = 
       match dict with
       | Empty -> Node (Empty, (key, value), Empty)
       | Node (l, (k, v), r) ->
         if k = key then
           Node (l, (k, value), r)
         else if key < k then
           Node (insert key value l, (k, v), r)
         else
           Node (l, (k, v), insert key value r)
     let rec print dict = 
       match dict with
       | Empty -> ()
       | Node (l, (k, v), r) ->
           print l;
           print_string (k ^ " : ");
           print_int v;
           print_string "\n";
           print r
end
  

(*----------------------------------------------------------------------------*]
 Funkcija [count (module Dict) list] prešteje in izpiše pojavitve posameznih
 elementov v seznamu [list] s pomočjo izbranega modula slovarjev.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # count (module Tree_dict) ["b"; "a"; "n"; "a"; "n"; "a"];;
 a : 3
 b : 1
 n : 2
 - : unit = ()
[*----------------------------------------------------------------------------*)
let count (module Dict : DICT) list =
  let rec aux dict = function
    | [] -> Dict.print dict
    | x::xs -> (
        match Dict.get x dict with
        | None -> aux (Dict.insert x 1 dict) xs
        | Some value -> aux (Dict.insert x (value + 1) dict) xs
    )
  in
  aux Dict.empty list