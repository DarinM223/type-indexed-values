structure Exn = struct type t = exn end
structure Fn = struct type ('a, 'b) t = 'a -> 'b end
structure Unit = struct type t = unit fun compare ((), ()) = EQUAL end
structure Bool = struct
   open Bool
   type t = bool
   fun isFalse b = not b
   fun isTrue b = b
end
structure Array = struct open Array type 'a t = 'a array end
structure ArraySlice = struct open ArraySlice type 'a t = 'a slice end
structure Char = struct open Char type t = char end
structure CharArray = struct open CharArray type t = array end
structure CharArraySlice = struct open CharArraySlice type t = slice end
structure CharVector = struct open CharVector type t = vector end
structure CharVectorSlice = struct open CharVectorSlice type t = slice end
structure Effect = struct type 'a t = 'a -> Unit.t end
structure FixedInt = struct open FixedInt type t = int end
structure Int = struct open Int type t = int end
structure Real = struct open Real type t = real end
structure LargeInt = struct open LargeInt type t = int end
structure LargeReal = struct open LargeReal type t = real end
structure LargeWord = struct open LargeWord type t = word end
structure List = struct open List type 'a t = 'a list end
structure Option = struct open Option type 'a t = 'a option end
structure Order = struct
   datatype order = datatype General.order
   type t = order
end
structure String = struct open String type t = string end
structure Substring = struct open Substring type t = substring end
structure Vector = struct open Vector type 'a t = 'a vector end
structure VectorSlice = struct open VectorSlice type 'a t = 'a slice end
structure Word = struct open Word type t = word end
structure Word8 = struct open Word8 type t = word end
structure Word8Array = struct open Word8Array type t = array end
structure Word8ArraySlice = struct open Word8ArraySlice type t = slice end
structure Word8Vector = struct open Word8Vector type t = vector end
structure Word8VectorSlice = struct
   open Word8VectorSlice
   type t = slice
end
structure Pair = struct
   type ('a, 'b) pair = 'a * 'b
   type ('a, 'b) t = ('a, 'b) pair
end
structure Product = struct
   datatype ('a, 'b) product = & of 'a * 'b
   type ('a, 'b) t = ('a, 'b) product
end
structure Ref = struct type 'a t = 'a ref end
structure Sum = struct
   datatype ('a, 'b) sum = INL of 'a | INR of 'b
   type ('a, 'b) t = ('a, 'b) sum
end
structure Sq = struct type 'a t = 'a * 'a end
structure Thunk = struct type 'a t = Unit.t -> 'a end
structure UnOp = struct type 'a t = 'a -> 'a end
structure UnPr = struct type 'a t = 'a -> Bool.t end
structure Fix = struct type 'a t = 'a UnOp.t -> 'a end
structure Reader = struct type ('a, 'b) t = 'b -> ('a * 'b) Option.t end
structure Writer = struct type ('a, 'b) t = 'a * 'b -> 'b end
structure Cmp = struct open Product type 'a t = 'a Sq.t -> Order.t end
structure BinOp = struct type 'a t = 'a Sq.t -> 'a end
structure BinPr = struct type 'a t = 'a Sq.t UnPr.t end
structure Emb = struct type ('a, 'b) t = ('a -> 'b) * ('b -> 'a Option.t) end
structure Iso = struct type ('a, 'b) t = ('a -> 'b) * ('b -> 'a) end
structure ShiftOp = struct type 'a t = 'a * Word.t -> 'a end
structure BinFn = struct type ('a, 'b) t = 'a Sq.t -> 'b end
structure IEEEReal = IEEEReal
structure Time = struct open Time type t = time end
structure CPS = struct type ('a, 'b) t = ('a -> 'b) -> 'b end
structure Id = struct type 'a t = 'a end

structure Fix = struct
   open Fix
   exception Fix
end

structure Fn = struct
   open Fn
   fun const x _ = x
   fun curry f x y = f (x, y)
   fun eta f x y = f x y
   fun fix f x = f (fix f) x
   fun flip f x y = f y x
   fun id x = x
   fun map (f, g) h = g o h o f
   fun iso ((a2c, c2a), (b2d, d2b)) = (map (c2a, b2d), map (a2c, d2b))
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

structure Basic = struct
   fun eq x y = x = y
   fun notEq x y = x <> y
   fun fail m = raise Fail m
   fun fails ms = fail (concat ms)
   fun failing m _ = fail m
   fun raising e _ = raise e
   fun recur x = Fn.flip Fn.fix x
   fun repeat f n x =
       if n < 0
       then raise Domain
       else recur (Word.fromInt n, x) (fn lp =>
               fn (0w0, x) => x
                | (n,   x) => lp (n-0w1, f x))
   fun undefined _ = fail "undefined"
end

structure Effect = struct
   open Effect
   val ignore = ignore
   val nop = ignore
   fun obs ef x = (ef x : Unit.t ; x)
   fun past ef x = (ef () : Unit.t ; x)
   fun tabulate n ef = ignore (Basic.repeat (fn i => (ef i : Unit.t ; i+1)) n 0)
   fun map b2a a = a o b2a
   fun iso (a2b, b2a) = (map b2a, map a2b)
end

structure Order = struct
   open Order
   val swap = fn LESS    => GREATER
               | EQUAL   => EQUAL
               | GREATER => LESS
   fun isEqual   x = x = EQUAL
   fun isGreater x = x = GREATER
   fun isLess    x = x = LESS
   val orWhenEq = fn (EQUAL, th) => th ()
                   | (other,  _) => other
end

structure Pair = struct
   open Pair

   val isoTuple2 as (fromTuple2, toTuple2) =
       (fn (a, b) => (a, b),
        fn (a, b) => (a, b))
   val isoTuple3 as (fromTuple3, toTuple3) =
       (fn (a, b, c) => ((a, b), c),
        fn ((a, b), c) => (a, b, c))
   val isoTuple4 as (fromTuple4, toTuple4) =
       (fn (a, b, c, d) => (((a, b), c), d),
        fn (((a, b), c), d) => (a, b, c, d))

   fun swap (a, b) = (b, a)
   fun swizzle ((a, b), (c, d)) = ((a, c), (b, d))

   fun fst (a, _) = a
   fun snd (_, b) = b

   fun app (ea, eb) (a, b) = (ea a : Unit.t ; eb b : Unit.t)
   fun appFst eA = app (eA, Effect.ignore)
   fun appSnd eB = app (Effect.ignore, eB)

   fun map (fa, fb) (a, b) = (fa a, fb b)
   fun mapFst fA = map (fA, Fn.id)
   fun mapSnd fB = map (Fn.id, fB)

   local
      fun mk p (fA, fB) (a, b) = let
         val a = fA a
      in
         if p a then fB b else a
      end
   in
      fun all     ? = mk Bool.isTrue   ?
      fun exists  ? = mk Bool.isFalse  ?
      fun equal   ? = mk Bool.isTrue   ? o swizzle
      fun collate ? = mk Order.isEqual ? o swizzle
   end

   fun foldl (fa, fb) ((a, b), s) = fb (b, fa (a, s))
   fun foldr (fa, fb) ((a, b), s) = fa (a, fb (b, s))

   fun thunk (na, nb) () = (na (), nb ())

   fun iso isos = map (map, map) (swizzle isos)
end


structure Sum = struct
   open Sum

   exception Sum

   fun sum (fA, fB) = fn INL a => fA a | INR b => fB b

   val swap = fn INL x => INR x | INR x => INL x

   val out = fn INL x => x | INR x => x
   val app = sum
   fun map (fA, fB) = sum (INL o fA, INR o fB)

   fun appL f = app (f, ignore)
   fun getL (INL x) _ = x | getL (INR _) x = x
   fun isL (INL _) = true | isL (INR _) = false
   fun mapL f = map (f, Fn.id)
   fun outL (INL l) = l | outL (INR _) = raise Sum

   fun appR f = appL f o swap
   fun getR ? = (getL o swap) ?
   fun isR ? = (isL o swap) ?
   fun mapR f = swap o mapL f o swap
   fun outR ? = (outL o swap) ?

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

   fun iso isos = Pair.map (map, map) (Pair.swizzle isos)
end

structure Product = struct
   open Product

   infix &

   val isoTuple2 as (fromTuple2, toTuple2) =
       (fn (a, b) => a & b,
        fn a & b => (a, b))
   val isoTuple3 as (fromTuple3, toTuple3) =
       (fn (a, b, c) => a & b & c,
        fn a & b & c => (a, b, c))
   val isoTuple4 as (fromTuple4, toTuple4) =
       (fn (a, b, c, d) => a & b & c & d,
        fn a & b & c & d => (a, b, c, d))

   fun swap (a & b) = b & a
   fun swizzle ((a & b), (c & d)) = ((a, c) & (b, d))

   fun fst (a & _) = a
   fun snd (_ & b) = b

   fun app (eA, eB) (a & b) = (eA a : Unit.t ; eB b : Unit.t)
   fun appFst eA = app (eA, Effect.ignore)
   fun appSnd eB = app (Effect.ignore, eB)

   fun map (fA, fB) (a & b) = fA a & fB b
   fun mapFst fA = map (fA, Fn.id)
   fun mapSnd fB = map (Fn.id, fB)

   local
      fun mk p (fA, fB) (a & b) = let
         val a = fA a
      in
         if p a then fB b else a
      end
   in
      fun all     ? = mk Bool.isTrue   ?
      fun exists  ? = mk Bool.isFalse  ?
      fun equal   ? = mk Bool.isTrue   ? o swizzle
      fun collate ? = mk Order.isEqual ? o swizzle
   end

   fun foldl (fA, fB) (a & b, s) = fB (b, fA (a, s))
   fun foldr (fA, fB) (a & b, s) = fA (a, fB (b, s))

   fun thunk (nA, nB) () = nA () & nB ()

   fun iso isos = Pair.map (map, map) (Pair.swizzle isos)
end

structure Iso = struct
   open Iso

   infix <-->

   val id = (Fn.id, Fn.id)

   val to = Pair.fst
   val from = Pair.snd
   val swap = Pair.swap

   fun (a2b, b2a) <--> (c2a, a2c) = (a2b o c2a, a2c o b2a)

   fun map (l, r) iso = r <--> iso <--> l
end

structure Thunk = struct
   open Thunk
   val mk = Fn.const
   fun map a2b a = a2b o a
   val isoValue = (fn th => th (), mk)
   fun iso (a2b, b2a) = (map a2b, map b2a)
end