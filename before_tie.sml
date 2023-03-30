structure Bool =
struct
  open Bool
  fun isFalse b = not b
  fun isTrue b = b
end
structure Fix = struct type 'a t = ('a -> 'a) -> 'a end

structure Fn =
struct
  type ('a, 'b) t = 'a -> 'b

  fun const x _ = x
  fun curry f x y = f (x, y)
  fun eta f x y = f x y
  fun fix f x =
    f (fix f) x
  fun flip f x y = f y x
  fun id x = x
  fun map (f, g) h = g o h o f
  fun iso ((a2c, c2a), (b2d, d2b)) =
    (map (c2a, b2d), map (a2c, d2b))
  fun seal f x () = f x
  fun uncurry f (x, y) = f x y
  val op o = op o
  fun <\ (x, f) y = f (x, y)
  fun \> (f, y) = f y
  fun /> (f, y) x = f (x, y)
  fun </ (x, f) = f x
  val >| = </
  val |< = \>
end

structure Order =
struct
  datatype order = datatype General.order
  type t = order
  val swap = fn LESS => GREATER | EQUAL => EQUAL | GREATER => LESS
  fun isEqual x = x = EQUAL
  fun isGreater x = x = GREATER
  fun isLess x = x = LESS
  val orWhenEq = fn (EQUAL, th) => th () | (other, _) => other
end

structure Pair =
struct
  type ('a, 'b) pair = 'a * 'b
  type ('a, 'b) t = ('a, 'b) pair

  val isoTuple2 as (fromTuple2, toTuple2) = (fn (a, b) => (a, b), fn (a, b) =>
    (a, b))
  val isoTuple3 as (fromTuple3, toTuple3) =
    (fn (a, b, c) => ((a, b), c), fn ((a, b), c) => (a, b, c))
  val isoTuple4 as (fromTuple4, toTuple4) =
    (fn (a, b, c, d) => (((a, b), c), d), fn (((a, b), c), d) => (a, b, c, d))

  fun swap (a, b) = (b, a)
  fun swizzle ((a, b), (c, d)) = ((a, c), (b, d))

  fun fst (a, _) = a
  fun snd (_, b) = b

  fun app (ea, eb) (a, b) =
    (ea a : unit; eb b : unit)
  fun appFst eA = app (eA, ignore)
  fun appSnd eB = app (ignore, eB)

  fun map (fa, fb) (a, b) = (fa a, fb b)
  fun mapFst fA = map (fA, Fn.id)
  fun mapSnd fB = map (Fn.id, fB)

  local
    fun mk p (fA, fB) (a, b) =
      let val a = fA a
      in if p a then fB b else a
      end
  in
    fun all ? = mk Bool.isTrue ?
    fun exists ? = mk Bool.isFalse ?
    fun equal ? =
      mk Bool.isTrue ? o swizzle
    fun collate ? =
      mk Order.isEqual ? o swizzle
  end

  fun foldl (fa, fb) ((a, b), s) =
    fb (b, fa (a, s))
  fun foldr (fa, fb) ((a, b), s) =
    fa (a, fb (b, s))

  fun thunk (na, nb) () = (na (), nb ())

  fun iso isos =
    map (map, map) (swizzle isos)
end

structure Sum =
struct
  datatype ('a, 'b) sum = INL of 'a | INR of 'b
  type ('a, 'b) t = ('a, 'b) sum
  exception Sum

  fun sum (fA, fB) =
    fn INL a => fA a | INR b => fB b

  val swap = fn INL x => INR x | INR x => INL x

  val out = fn INL x => x | INR x => x
  val app = sum
  fun map (fA, fB) =
    sum (INL o fA, INR o fB)

  fun appL f = app (f, ignore)
  fun getL (INL x) _ = x
    | getL (INR _) x = x
  fun isL (INL _) = true
    | isL (INR _) = false
  fun mapL f = map (f, Fn.id)
  fun outL (INL l) = l
    | outL (INR _) = raise Sum

  fun appR f = appL f o swap
  fun getR ? =
    (getL o swap) ?
  fun isR ? =
    (isL o swap) ?
  fun mapR f =
    swap o mapL f o swap
  fun outR ? =
    (outL o swap) ?

  fun mapLR f = map (f, f)

  fun equal (eqA, eqB) =
    fn (INL l, INL r) => eqA (l, r)
     | (INL _, INR _) => false
     | (INR _, INL _) => false
     | (INR l, INR r) => eqB (l, r)

  fun collate (cmpA, cmpB) =
    fn (INL l, INL r) => cmpA (l, r)
     | (INL _, INR _) => LESS
     | (INR _, INL _) => GREATER
     | (INR l, INR r) => cmpB (l, r)

  fun iso isos =
    Pair.map (map, map) (Pair.swizzle isos)
end

structure Product =
struct
  datatype ('a, 'b) product = & of 'a * 'b
  type ('a, 'b) t = ('a, 'b) product

  infix &

  val isoTuple2 as (fromTuple2, toTuple2) = (fn (a, b) => a & b, fn a & b =>
    (a, b))
  val isoTuple3 as (fromTuple3, toTuple3) =
    (fn (a, b, c) => a & b & c, fn a & b & c => (a, b, c))
  val isoTuple4 as (fromTuple4, toTuple4) =
    (fn (a, b, c, d) => a & b & c & d, fn a & b & c & d => (a, b, c, d))

  fun swap (a & b) = b & a
  fun swizzle ((a & b), (c & d)) =
    ((a, c) & (b, d))

  fun fst (a & _) = a
  fun snd (_ & b) = b

  fun app (eA, eB) (a & b) =
    (eA a : unit; eB b : unit)
  fun appFst eA = app (eA, ignore)
  fun appSnd eB = app (ignore, eB)

  fun map (fA, fB) (a & b) = fA a & fB b
  fun mapFst fA = map (fA, Fn.id)
  fun mapSnd fB = map (Fn.id, fB)

  local
    fun mk p (fA, fB) (a & b) =
      let val a = fA a
      in if p a then fB b else a
      end
  in
    fun all ? = mk Bool.isTrue ?
    fun exists ? = mk Bool.isFalse ?
    fun equal ? =
      mk Bool.isTrue ? o swizzle
    fun collate ? =
      mk Order.isEqual ? o swizzle
  end

  fun foldl (fA, fB) (a & b, s) =
    fB (b, fA (a, s))
  fun foldr (fA, fB) (a & b, s) =
    fA (a, fB (b, s))

  fun thunk (nA, nB) () = nA () & nB ()

  fun iso isos =
    Pair.map (map, map) (Pair.swizzle isos)
end

structure Iso =
struct
  type ('a, 'b) t = ('a -> 'b) * ('b -> 'a)

  infix <-->

  val id = (Fn.id, Fn.id)

  val to = Pair.fst
  val from = Pair.snd
  val swap = Pair.swap

  fun (a2b, b2a) <--> (c2a, a2c) = (a2b o c2a, a2c o b2a)

  fun map (l, r) iso = r <--> iso <--> l
end

structure Thunk =
struct
  type 'a t = unit -> 'a
  val mk = Fn.const
  fun map a2b a = a2b o a
  val isoValue = (fn th => th (), mk)
  fun iso (a2b, b2a) = (map a2b, map b2a)
end
