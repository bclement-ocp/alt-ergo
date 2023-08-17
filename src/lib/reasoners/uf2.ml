module St = Store.Historical
module Ex = Explanation

type ex = Ex.t

type -'a store = 'a St.t

type 'a tree = Nil | Node of 'a * 'a tree list

let append t t' =
  match t, t' with
  | Nil, t | t, Nil -> t
  | Node (root, ts), t' -> Node (root, t' :: ts)

type 'a class' = 'a tree

let croot = function
  | Nil -> None
  | Node (root, _) -> Some root

let rec iter f = function
  | Nil -> ()
  | Node (x, ts) -> f x; List.iter (iter f) ts

let rec fold f acc = function
  | Nil -> acc
  | Node (x, ts) ->
    List.fold_left (fold f) (f acc x) ts

type ('a, 'b) data =
    Root of { value : 'a ; rank : int ; tree : 'b tree }
  | Link of ('a, 'b) cell * ex

and ('a, 'b) cell = ('a, 'b) data St.Ref.t

let cell ?term value =
  let tree =
    match term with
    | Some term -> Node (term, [])
    | None -> Nil
  in
  St.Ref.make @@ Root { value; rank = 0 ; tree }

let rec find s c =
  match St.Ref.get s c with
  | Root _ -> c, Ex.empty
  | Link (c', ex) ->
    let r, ex' = find s c' in
    let ex = Ex.union ex ex' in
    St.Ref.set s c @@ Link (r, ex);
    r, ex

let union ?(cmp = fun _ _ -> 0) s x y ex =
  let x, exx = find s x and y, exy = find s y in
  let ex = Ex.union exx ex in
  let ex = Ex.union exy ex in
  if x != y then
    match St.Ref.get s x, St.Ref.get s y with
    | Root { value = vx; rank = rx ; tree = tx }
    , Root { value = vy; rank = ry ; tree = ty } ->
      if rx < ry then (
        let value, tree =
          if cmp vx vy >= 0 then
            vy, append ty tx
          else
            vx, append tx ty
        in
        let rank = ry in
        St.Ref.set s x @@ Link (y, ex);
        St.Ref.set s y @@ Root { value; rank; tree }
      ) else (
        let value, tree =
          if cmp vx vy <= 0 then
            vx, append tx ty
          else
            vy, append ty tx
        in
        let rank = if rx = ry then rx + 1 else rx in
        St.Ref.set s y @@ Link (x, ex);
        St.Ref.set s x @@ Root { value; rank; tree }
      );

      ex

    | _ -> assert false
  else
    ex

let root s c =
  find (St.unsafe s) c

let find s c =
  let x, ex = root s c in
  match St.Ref.get s x with
  | Root { value; tree; rank = _ } -> value, tree, ex
  | _ -> assert false

let class' s c =
  let _, class', _ = find s c in
  class'

let value s c =
  let root, _, _= find s c in
  root
