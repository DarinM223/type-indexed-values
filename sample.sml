infix &

fun option t =
  let open Show Sum
  in inj (fn NONE => INL () | SOME v => INR v) (data (C0 "NONE" + C1 "SOME" t))
  end

datatype 'a graph = VTX of 'a * 'a graph list ref
fun arcs (VTX (_, r)) = r

fun graph a =
  let
    open Tie Show Product
  in
    fix Y (fn graph_a =>
      inj (fn VTX (x, y) => x & y) (data (C1 "VTX" (tuple
        (U a * U (refc (list graph_a)))))))
  end

val a_graph =
  let
    val a = VTX (1, ref [])
    val b = VTX (2, ref [])
    val c = VTX (3, ref [])
    val d = VTX (4, ref [])
    val e = VTX (5, ref [])
    val f = VTX (6, ref [])
  in
    arcs a := [b, d];
    arcs b := [c, e];
    arcs c := [a, f];
    arcs d := [f];
    arcs e := [d];
    arcs f := [e];
    a
  end

val _ =
  let
    open Show
  in
    print (show (list int) [1, 3, 4] ^ "\n");
    print (show (option (option string)) (SOME (SOME "hello")) ^ "\n");
    print (show (graph int) a_graph ^ "\n")
  end
