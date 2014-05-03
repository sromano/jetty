open Expression
open Type
open Utils
open Library

let match_template (i2n,_,_) template i = 
  let bindings = ref [] in
  let rec m t j = 
    match t with
    | Terminal(name,_,_) when name.[0] = '?' -> begin
        let name_ID = int_of_string @@ String.sub name 1 (String.length name - 1) in
        try
          let k = List.assoc name_ID !bindings in
          k = j
        with _ -> (bindings := (name_ID,j) :: !bindings; true)
      end
    | Application(f,x) -> begin
        try
          match Hashtbl.find i2n j with
          | ExpressionLeaf(_) -> false
          | ExpressionBranch(f_,x_) -> m f f_ && m x x_
        with _ -> raise (Failure "match_template, ID not in graph")
      end
    | Terminal(name,_,_) -> begin
        try
          match Hashtbl.find i2n j with
          | ExpressionLeaf(Terminal(name_,_,_)) -> name == name_
          | _ -> false
        with _ -> raise (Failure "match_template, ID not in graph")
      end
  in if m template i then Some(!bindings) else None
    
let apply_template dagger template bindings = 
  let rec apply t = 
    match t with
    | Terminal(name,_,_) when name.[0] = '?' -> begin
        let name_ID = int_of_string @@ String.sub name 1 (String.length name - 1) in
        try
          extract_expression dagger @@ List.nth bindings name_ID
        with _ -> raise (Failure "apply_template: unbound")
      end
    | Terminal(_,_,_) -> t
    | Application(f,x) -> 
      Application(apply f,apply x)
  in apply template

let backward_children dagger grammar request rewrites j = 
  let (i2n,_,_) = dagger in
  let rec children i = 
    let head_rewrites = rewrites |> List.fold_left (fun a (template,handler) -> 
        match match_template dagger template i with
        | None -> a
        | Some(bindings) -> (handler bindings)::a) [] in
    match Hashtbl.find i2n i with
    | ExpressionLeaf(_) -> head_rewrites
    | ExpressionBranch(f,x) -> 
      let left = extract_expression dagger f in
      let right = extract_expression dagger x in
      let left_children = children f |> List.map (fun l -> 
          Application(l,right)) in
      let right_children = children x |> List.map (fun r -> 
          Application(left,r)) in
      head_rewrites @ left_children @ right_children
  in children j |> List.map (fun e -> (likelihood_option grammar request e, e)) |>
     List.filter (compose is_some fst) |> 
     List.map (fun (l,e) -> (insert_expression dagger e, get_some l))

(* let backward_enumerate dagger grammar likelihoods rewrites size i = *)
