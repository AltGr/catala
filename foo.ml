
(* Scope Stest *)
let stest : Stest_in.t -> Stest.t = fun _ ->
  let s__1: S.t = (let result : S.t = (s ({S_in.a_in = Optional.Absent})) in
                   (let result__1 : S.t = ({S.a = (result.S.a)}) in
                    (if true then result__1 else result__1))) in
  {Stest.s = s__1}
