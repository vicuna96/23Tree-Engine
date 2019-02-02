exception Unimplemented

module type Formattable = sig
	type t
	val format : Format.formatter -> t -> unit
end

module type Comparable = sig
	type t
	val compare : t -> t -> [ `EQ | `GT | `LT ]
	include Formattable with type t := t
end

type ('k,'v) tree23 =
	| Leaf
	| Twonode of ('k,'v) twonode
	| Threenode of ('k,'v) threenode
and ('k,'v) twonode = {
	left2  : ('k,'v) tree23;
	value  : 'k * 'v;
	right2 : ('k,'v) tree23;
}
and ('k,'v) threenode = {
	left3   : ('k,'v) tree23;
	lvalue  : 'k * 'v;
	middle3 : ('k,'v) tree23;
	rvalue  : 'k * 'v;
	right3  : ('k,'v) tree23;
}

module type Dictionary = sig
	module Key : Comparable
	module Value : Formattable
	type key = Key.t
	type value = Value.t
	type t
	val rep_ok : t  -> t
	val empty : t
	val is_empty : t -> bool
	val size : t -> int
	val insert : key -> value -> t -> t
	val member : key -> t -> bool
	val find : key -> t -> value option
	val remove : key -> t -> t
	val choose : t -> (key * value) option
	val fold : (key -> value -> 'acc -> 'acc) -> 'acc -> t -> 'acc
	val to_list : t -> (key * value) list
	val expose_tree : t -> (key, value) tree23
	val format : Format.formatter -> t -> unit
end

module type DictionaryMaker =
	functor (K : Comparable) (V : Formattable)
		-> Dictionary with module Key = K and module Value = V

module MakeListDictionary (K : Comparable) (V : Formattable) = struct
	module Key = K
	module Value = V
	type key = K.t
	type value = V.t

(* AF: A [(key * value ) list] is dictionary where each entry (key * value)
 *     represents the pairing of [key] to [value].
 * RI: [(key * value) list] has the [key] binded to [value] if the first
 *     occurance of [key] is [(key,value)] in the list *)
	type t = (key * value) list


	let empty = []

	let is_empty d = d=[]

 let size d =
   List.fold_left (fun x y -> x+1) 0 d

	let insert k v d =
			(k,v)::d

 let rec remove k d =
   let d' = List.remove_assoc k d in
   if List.mem_assoc k d' then
     remove k d'
   else
     d'

	let find k d =
		List.assoc_opt k d

	let member k d =
		List.mem_assoc k d

	let choose d =
		match d with
		| []-> None
		| h::_-> Some h

 (*[help_dupl [] lst] is the association list [lst'] with only the newest
  * binding [value] per [key] *)
 let rec help_dupl accu = function
   | [] -> accu
   | (k,v)::t ->
     if List.mem_assoc k accu then
       help_dupl accu t
     else
       help_dupl ((k,v)::accu) t

 (* [compares (x,a) (y,b)] is 0 if [x] and [y] are aqual, 1 if [x] is greater
  * than [y], and -1 if [x] is greater than [y] according to their compare
  * function.
  * requires: [x] and [y] are of type Key.t *)
 	let compares (x,_) (y,_) =
 		match Key.(compare x y) with
 		| `EQ -> 0
 		| `GT -> 1
 		| `LT -> -1

  let to_list d =
    d|>help_dupl [] |>List.sort_uniq compares

 let rep_ok d = to_list d

  let fold f init d =
    let f_double f init (x,y) = f x y init in
		d
    |> to_list
		|> List.fold_left (f_double f) init

 let expose_tree d =
   failwith "not a 2-3 tree"

let format fmt d =
  Format.fprintf fmt "[";
  let f (k,v) = Format.fprintf fmt "%a," K.format k;
                Format.fprintf fmt "%a; " V.format v; in
    List.iter f d;
    Format.fprintf fmt "]"

end

module MakeTreeDictionary (K : Comparable) (V : Formattable) = struct
	module Key = K
	module Value = V
	type key = K.t
	type value = V.t

 type t = (key,value) tree23

(* [flip_f f x y] is f y x, that is, flip_f flips the order of argument
 * application for *)
let flip_f f x y = f y x

(* [depth_help d] is the depth of d, assuming d is balanced. The [depth_help Leaf]
 * is defined to be 0. If d is unbalanced, then [depth_help d] is -1 *)
 let rec depth_help = function
   | Leaf -> 0
   | Twonode x ->
     let lft = depth_help x.left2 in
     let rgt = depth_help x.right2 in
     if lft = -1 || rgt = -1 then -1
     else if lft <> rgt then -1
     else lft+1
   | Threenode x ->
     let lft3 = depth_help x.left3 in
     let midd = depth_help x.middle3 in
     let rgt3 = depth_help x.right3 in
     if lft3 = -1 || midd = -1 || rgt3 = -1 then -1
     else if lft3 <> midd || midd <> rgt3 then -1
     else lft3+1

(* [help_to_list d] is the list of all elements in [d] in order from
 * left to right. In particular, if [d] satisfies the RI, then
 * [help_to_list d] returns a list representation of [d] in increasing order *)
 let rec help_to_list = function
   | Leaf -> []
   | Twonode x ->
     help_to_list x.left2
     |> List.rev
     |> flip_f List.rev_append (x.value::help_to_list x.right2)
   | Threenode x ->
     help_to_list x.left3
     |> List.rev
     |> flip_f List.rev_append (x.lvalue::help_to_list x.middle3)
     |> flip_f List.rev_append (x.rvalue::help_to_list x.right3)

(*[check_order boo d] is true if the keys in the association list [d] are
 * in increasing order and [boo]=true, false otherwise.
 * requires: [d] : [(key*value) list] *)
 let rec check_order boo = function
   | [] -> boo
   | h::[] -> boo
   | (h,_)::(t,_)::[] -> Key.(compare h t = `LT) && boo
   | (h,_)::(m,x)::t ->
     check_order (Key.(compare h m = `LT) && boo) ((m,x)::t)

 let rep_ok d =
   if depth_help d <> -1 && (d |> help_to_list |> check_order true) then
     d
   else
     failwith "Does not satisfy RI"

	let empty = Leaf

	let is_empty d = d=Leaf

	let rec size = function
   | Leaf -> 0
   | Twonode x -> 1 + size x.left2 + size x.right2
   | Threenode x -> 2 + size x.left3 + size x.middle3 + size x.right3

 (* AF: A [Tree ('k,'v) tree23] is a regular 2-3 tree whose nodes contain
  * key-value pairs of type ['k*'v]. A [Kickup ('k,'v) twonode] is a variation
  * of this wher this instance of [tree] is in the process of being
  * kicked up until the RI for 23 trees is satisfied.
  * RI: The conjunction of the RIs for [twonode] and [threenode]
  * which must also hold for x and y in Tree x and Kickup y. *)
 type tree =
   | Tree of (key,value) tree23
   | Kickup of (key,value) twonode

 (*[three_n l lv m rv r] returns the Threenode with left subtree l, middle
  * subtree m, right subtree r, left value lv and right value rv. *)
 let three_n l lv m rv r =
   Threenode {left3=l;lvalue=lv;middle3=m;rvalue=rv;right3=r}

 (*[kick_two l m r] returns the Kickup tree with leftsubtree l, right
  * subtree r, and value v*)
 let kick_two l v r =
   Kickup ({left2=l;value=v;right2=r})

 (*branch types used for passing information about where to insert in a 23tree *)
 type branch = L | M | R

 let rec insert_help k v tree =
   match tree with
   | Leaf -> kick_two Leaf (k,v) Leaf
   | Twonode {left2=l;value=(k',v');right2=r} ->
     begin
     match K.compare k' k with
     | `EQ ->  Tree (Twonode {left2=l;value=(k,v);right2=r})
     | `LT -> two_help `LT (insert_help k v r) l k' v' r
     | `GT -> two_help `GT (insert_help k v l) l k' v' r
     end
   | Threenode {left3=l;lvalue=(lk,lv);middle3=m;rvalue=(rk,rv);right3=r} ->
     match K.compare lk k with
     | `EQ ->  Tree (three_n l (k,v) m (rk,rv) r)
     | `GT -> three_help L (insert_help k v l) l (lk,lv) m (rk,rv) r
     | `LT ->
       match K.compare rk k with
       | `EQ ->  Tree (three_n l (lk,lv) m (k,v) r)
       | `GT -> three_help M (insert_help k v m) l (lk,lv) m (rk,rv) r
       | `LT -> three_help R (insert_help k v r) l (lk,lv) m (rk,rv) r

(* [two_help c tree l k v r] is the threenode [tree'] that absorbs the [tree]
 * as well as the trees [l], [r], and the value [(k,v)].
 * If c=`LT, the tree becomes a tree with left value the same as the value
 * in [tree], right value is [(k,v)], while if c=`GT then the left value
 * is [(k,v)], right value is the same as the [tree]'s value, and the subtrees
 * of [tree] and either [l] or [r] are placed satisfying the RI. *)
 and two_help compar tree' l k' v' r =
   match tree' with
   | Tree x ->
     if compar = `GT then
       Tree (Twonode {left2=x;value=(k',v');right2=r})
     else
       Tree (Twonode {left2=l;value=(k',v');right2=x})
   | Kickup x ->
     let node =
       if compar = `GT then
         three_n x.left2 x.value x.right2 (k',v') r
       else
         three_n l (k',v') x.left2 x.value x.right2
     in Tree node

 (* [three_help c tree l lv m rv r] is the Kickup [tree'] that absorbs the [tree]
  * as well as the trees [l], [m], [r], and the values [lv] and [rv].
  * If c=L, [tree'] node has value [lv], if c=R then [rv], and if c=M then
  * the [tree'] node's value is the same as [tree] node's value. All other
  * subtrees and values are absorved in the trivial way that satisfies the RI. *)
 and three_help compar tree' l lval m rval r =
   match compar with
   | L ->
     begin
       match tree' with
       | Tree x -> Tree (three_n x lval m rval r)
       | Kickup x ->
         let right = Twonode {left2=m;value=rval;right2=r} in
         Kickup ({left2=Twonode x;value=lval;right2=right})
     end
   | M ->
     begin
       match tree' with
       | Tree x -> Tree (three_n l lval x rval r)
       | Kickup x ->
         let left = Twonode {left2=l;value=lval;right2=x.left2} in
         let right = Twonode {left2=x.right2;value=rval;right2=r} in
         Kickup ({left2=left;value=x.value;right2=right})
     end
   | R ->
     begin
       match tree' with
       | Tree x -> Tree (three_n l lval m rval x)
       | Kickup x ->
         let left = Twonode {left2=l;value=lval;right2=m} in
         Kickup ({left2=left;value=rval;right2=Twonode x}) (*bug !!!!!*)
     end

 (*[get_tree tree] returns the 23tree stored inside [tree] *)
 let get_tree = function
   | Tree x -> x
   | Kickup x -> Twonode x

 let insert k v d =
   insert_help k v d
   |> get_tree

	let remove k d =
		d

	let rec find k d =
   match d with
   | Leaf -> None
   | Twonode x ->
      begin
      match Key.compare k (fst x.value) with
      | `EQ -> Some (snd x.value)
      | `LT -> find k x.left2
      | `GT -> find k x.right2
      end
   | Threenode x ->
      begin
      match Key.compare k (fst x.lvalue) with
      | `EQ -> Some (snd x.lvalue)
      | `LT -> find k x.left3
      | `GT ->
        begin
        match Key.compare k (fst x.rvalue) with
        | `EQ -> Some (snd x.rvalue)
        | `LT -> find k x.left3
        | `GT -> find k x.right3
        end
      end

	let member k d =
   find k d |> (<>) None

	let choose = function
   | Leaf -> None
   | Twonode x -> Some x.value
   | Threenode x -> Some x.lvalue

	let to_list =
		help_to_list

	let expose_tree d =
		d

 let fold f init d =
   let f_double f init (x,y) = f x y init in
   d|>to_list|> List.fold_left (f_double f) init

 let format fmt d =
   let lst = d|> to_list in
   Format.fprintf fmt "[";
   let f (k,v) = Format.fprintf fmt "%a," K.format k;
                 Format.fprintf fmt "%a; " V.format v; in
     List.iter f lst;
     Format.fprintf fmt "]"

end

module type Set = sig
	module Elt : Comparable
	type elt = Elt.t
	type t
	val rep_ok : t  -> t
	val empty : t
	val is_empty : t -> bool
	val size : t -> int
	val insert : elt -> t -> t
	val member : elt -> t -> bool
	val remove : elt -> t -> t
	val union : t -> t -> t
	val intersect : t -> t -> t
	val difference : t -> t -> t
	val choose : t -> elt option
	val fold : (elt -> 'acc -> 'acc) -> 'acc -> t -> 'acc
	val to_list : t -> elt list
	val format : Format.formatter -> t -> unit
end

(* Encapsulates the type unit so that it can be passed in DictionaryMaker
	 maker to generate MakeSetOfDictionary*)
module UnitFormattable = struct
	type t = unit
	let format fmt d =
		Format.fprintf fmt "<abstr>"
end


module MakeSetOfDictionary (C : Comparable) (DM:DictionaryMaker) = struct
	module Elt = C
	type elt = Elt.t
 module D = DM(Elt)(UnitFormattable)

	type t = D.t

	let rep_ok s =
		D.rep_ok s

	let empty =
		D.empty

	let is_empty s =
		D.is_empty s

	let size s =
		D.size s

	let insert x s =
	 D.insert x () s

	let member x s =
		D.member x s

	let remove x s =
		D.remove x s

 let choose s=
	 match D.choose s with
	 | None -> None
	 | Some (x,_)-> Some x

let fold f init s =
	 let f_set x y z = f x z  in
	 D.fold f_set init s

 let union s1 s2 =
   let add x accu = insert x accu in
   fold add s1 s2

(*[modify s1 f x accu] is the set [accu'] that results from the application
 * of f on [x accu] if is in s1, or [accu'] otherwise *)
 let modify s1 f x accu =
   if member x s1 then f x accu
   else accu

 let intersect s1 s2 =
   fold (modify s1 insert) empty s2

 let difference s2 s1 =
   fold (modify s1 remove) s2 s2

	let to_list s =
   List.rev_map (fun (x,_)->x) (D.to_list s)
   |> List.rev

let format fmt d =
  let lst = d|>to_list in
  Format.fprintf fmt "[";
  List.iter (fun elt -> Format.fprintf fmt "%a; " C.format elt) lst;
  Format.fprintf fmt "]"
end

module CompareInt = struct
  type t=int

  let compare (x:int) (y:int) =
    match compare x y with
    | 0 -> `EQ
    | x -> if x>0 then `GT else `LT

  let format fmt d =
    Format.fprintf fmt "<abstr>"
end

module ITree = MakeTreeDictionary(CompareInt)(CompareInt)
