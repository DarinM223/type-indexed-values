signature ETAEXP' =
sig
  type 'a etaexp_dom
  and 'a etaexp_cod
  type 'a etaexp = 'a etaexp_dom -> 'a etaexp_cod
end

signature TIE =
sig
  include ETAEXP'
  type 'a t = 'a etaexp

  val fix: 'a t -> 'a Fix.t
  val pure: ('a * 'a UnOp.t) Thunk.t -> 'a t
  val tier: ('a * 'a Effect.t) Thunk.t -> 'a t
  val id: 'a -> 'a t
  val iso: 'b t -> ('a, 'b) Iso.t -> 'a t
  val product: 'a t * ('a -> 'b t) -> ('a, 'b) Product.t t
  val *` : 'a t * 'b t -> ('a, 'b) Product.t t
  val tuple2: 'a t * 'b t -> ('a * 'b) t
  val function: ('a -> 'b) t
end
