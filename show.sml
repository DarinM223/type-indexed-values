infixr -->
infix &
infix <\

signature SHOW =
sig
  type 'a t (* complete type-index *)
  type 'a s (* incomplete sum *)
  type ('a, 'k) p (* incomplete product *)
  type u (* tuple or unlabelled product *)
  type l (* record or labelled product *)

  val show: 'a t -> 'a -> string

  (* user-defined types *)
  val inj: ('a -> 'b) -> 'b t -> 'a t

  (* tuples and records *)
  val * : ('a, 'k) p * ('b, 'k) p -> (('a, 'b) Product.product, 'k) p

  val U: 'a t -> ('a, u) p
  val L: string -> 'a t -> ('a, l) p

  val tuple: ('a, u) p -> 'a t
  val record: ('a, l) p -> 'a t

  (* datatypes *)
  val + : 'a s * 'b s -> (('a, 'b) Sum.sum) s

  val C0: string -> unit s
  val C1: string -> 'a t -> 'a s

  val data: 'a s -> 'a t

  val Y: 'a t Tie.t

  (* exceptions *)
  val exn: exn t
  val regExn: (exn -> ('a * 'a s) option) -> unit

  (* some built-in type constructors *)
  val refc: 'a t -> 'a ref t
  val array: 'a t -> 'a array t
  val list: 'a t -> 'a list t
  val vector: 'a t -> 'a vector t
  val --> : 'a t * 'b t -> ('a -> 'b) t

  (* some built-in base types *)
  val string: string t
  val unit: unit t
  val bool: bool t
  val char: char t
  val int: int t
  val word: word t
  val real: real t
end

structure SmlSyntax =
struct

  local structure CV = CharVector and C = Char
  in
    val isSym = Char.contains "!%&$#+-/:<=>?@\\~`^|*"

    fun isSymId s =
      0 < size s andalso CV.all isSym s

    fun isAlphaNumId s =
      0 < size s andalso C.isAlpha (CV.sub (s, 0))
      andalso CV.all (fn c => C.isAlphaNum c orelse #"'" = c orelse #"_" = c) s

    fun isNumLabel s =
      0 < size s andalso #"0" <> CV.sub (s, 0) andalso CV.all C.isDigit s

    fun isId s = isAlphaNumId s orelse isSymId s

    fun isLongId s =
      let open Fn
      in List.all isId (String.fields (#"." <\ op=) s)
      end

    fun isLabel s = isId s orelse isNumLabel s
  end
end

structure Show =
struct
  datatype 'a t = IN of exn list * 'a -> bool * string
  type 'a s = 'a t
  type ('a, 'k) p = 'a t
  type u = unit
  type l = unit

  fun show (IN t) x =
    #2 (t ([], x))

  (* user-defined types *)
  fun inj inj (IN b) =
    IN (b o Pair.map (Fn.id, inj))

  local
    fun surround pre suf (_, s) =
      (false, concat [pre, s, suf])
    fun parenthesize x =
      if #1 x then surround "(" ")" x else x
    fun construct tag =
      (fn (_, s) => (true, concat [tag, " ", s])) o parenthesize
    fun check p m s =
      if p s then () else raise Fail (m ^ s)
  in
    (* tuples and records *)
    fun (IN l) * (IN r) =
      let
        open Product
      in
        IN (fn (rs, a & b) =>
          (false, concat [#2 (l (rs, a)), ", ", #2 (r (rs, b))]))
      end

    val U = Fn.id
    fun L l =
      ( check SmlSyntax.isLabel "Invalid label: " l
      ; fn IN t => IN (surround (l ^ " = ") "" o t)
      )

    fun tuple (IN t) =
      IN (surround "(" ")" o t)
    fun record (IN t) =
      IN (surround "{" "}" o t)

    (* datatypes *)
    fun (IN l) + (IN r) =
      IN (fn (rs, Sum.INL a) => l (rs, a) | (rs, Sum.INR b) => r (rs, b))

    fun C0 c =
      (check SmlSyntax.isId "Invalid constructor: " c; IN (Fn.const (false, c)))
    fun C1 c (IN t) =
      (check SmlSyntax.isId "Invalid constructor: " c; IN (construct c o t))

    val data = Fn.id

    fun Y ? =
      Tie.iso Tie.function (fn IN x => x, IN) ?

    (* exceptions *)
    local val handlers = ref ([] : (exn -> unit t option) list)
    in
      val exn = IN (fn (rs, e) =>
        let
          fun lp [] =
                C0 (concat ["<exn:", General.exnName e, ">"])
            | lp (f :: fs) =
                case f e of
                  NONE => lp fs
                | SOME t => t
          val IN f = lp (!handlers)
        in
          f (rs, ())
        end)
      fun regExn f =
        handlers
        :=
        (Option.map (fn (x, IN f) => IN (fn (rs, ()) => f (rs, x))) o f)
        :: !handlers
    end

    (* some built-in type constructors *)
    local
      fun cyclic (IN t) =
        let
          exception E of ''a * bool ref
        in
          IN (fn (rs, v: ''a) =>
            let
              val idx: exn list -> string = Int.toString o length
              fun lp (E (v', c) :: rs) =
                    if v' <> v then lp rs
                    else (c := false; (false, "%" ^ idx rs))
                | lp (_ :: rs) = lp rs
                | lp [] =
                    let
                      val c = ref true
                      val r = t (E (v, c) :: rs, v)
                    in
                      if !c then r else surround "" (" as %" ^ idx rs) r
                    end
            in
              lp rs
            end)
        end

      fun aggregate pre suf toList (IN t) =
        IN
          (surround pre suf
           o
           (fn (rs, a) =>
              ( false
              , String.concatWith ", " (map (#2 o Fn.curry t rs) (toList a))
              )))
    in
      fun refc ? =
        (cyclic o inj ! o C1 "ref") ?
      fun array ? =
        (cyclic o aggregate "[|" "|]" (Array.foldr op:: [])) ?
      fun list ? =
        aggregate "[" "]" Fn.id ?
      fun vector ? =
        aggregate "#[" "]" (Vector.foldr op:: []) ?
    end

    fun (IN _) --> (IN _) =
      IN (Fn.const (false, "<fn>"))

    (* some built-in base types *)
    local
      fun mk toS =
        (fn x => (false, x)) o toS o (fn (_, x) => x)
    in
      val string = IN (surround "\"" "\"" o mk (String.translate Char.toString))
      val unit = IN (mk (fn () => "()"))
      val bool = IN (mk Bool.toString)
      val char = IN (surround "#\"" "\"" o mk Char.toString)
      val int = IN (mk Int.toString)
      val word = IN (surround "0wx" "" o mk Word.toString)
      val real = IN (mk Real.toString)
    end
  end
end

(* Handlers for standard top-level exceptions *)
val () =
  let
    open Show
    fun E0 name =
      SOME ((), C0 name)
  in
    regExn
      (fn Bind => E0 "Bind"
        | Chr => E0 "Chr"
        | Div => E0 "Div"
        | Domain => E0 "Domain"
        | Empty => E0 "Empty"
        | Match => E0 "Match"
        | Option => E0 "Option"
        | Overflow => E0 "Overflow"
        | Size => E0 "Size"
        | Span => E0 "Span"
        | Subscript => E0 "Subscript"
        | _ => NONE);
    regExn (fn Fail s => SOME (s, C1 "Fail" string) | _ => NONE)
  end
