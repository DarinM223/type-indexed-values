fun option t =
  let
    open Show Sum
  in
    inj (fn NONE => INL ()
     | SOME v => INR v)
     (data (C0 "NONE" + C1 "SOME" t))
  end

val _ =
  let
    open Show
  in
    print (show (list int) [1, 3, 4] ^ "\n");
    print (show (option (option string)) (SOME (SOME "hello")) ^ "\n")
  end