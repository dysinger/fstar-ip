(**
Network.IP — Shared utilities for IP address codecs.

Drop and list lemmas used by both [Network.IPv4] and [Network.IPv6].

@header Network.IP

@section Functions
- [drop] — drop n elements from front of list
- [lemma_drop_append_length] — drop (|ds|) (ds @ suffix) == suffix
*)

module Network.IP

open FStar.List.Tot

(** Drop [n] elements from the front of a list.
    @param n Number of elements to drop.
    @param l Input list.
    @returns [l] without its first [n] elements.
             If [n] exceeds the list length, returns [[]]. *)
let rec drop (#a:Type) (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then l else match l with [] -> [] | _ :: tl -> drop (n-1) tl

(** Lemma: dropping the length of a prefix from the concatenation
    yields the suffix.  [drop (length ds) (ds @ suffix) == suffix].

    Auxiliary recursive form — lifted to top-level from local [let rec]
    for proper SMT encoding.  Prove by induction on [ds].
    @param ds Prefix list.
    @param suffix Suffix list.
    @returns Lemma — [drop (|ds|) (ds @ suffix) = suffix]. *)
let rec lemma_drop_append_length_aux (#a:Type) (ds suffix: list a) : Lemma
  (ensures drop (length ds) (ds @ suffix) == suffix) (decreases ds)
  = match ds with [] -> () | _ :: tl -> lemma_drop_append_length_aux tl suffix

(** Thin wrapper around [lemma_drop_append_length_aux] for public
    API hygiene.  The aux lemma is recursive; this alias presents
    a clean non-recursive interface.
    @param ds Prefix list.
    @param suffix Suffix list.
    @returns Lemma — [drop (|ds|) (ds @ suffix) = suffix]. *)
let lemma_drop_append_length (#a:Type) (ds suffix: list a) : Lemma
  (ensures drop (length ds) (ds @ suffix) == suffix)
  = lemma_drop_append_length_aux ds suffix

(** Lemma: dropping elements never increases list length.
    [length (drop n l) <= length l].
    @param n Number of elements to drop.
    @param l Input list.
    @returns Lemma — [|drop n l| <= |l|]. *)
let rec lemma_drop_length_bound (#a:Type) (n: nat) (l: list a) : Lemma
  (ensures List.Tot.length (drop n l) <= List.Tot.length l)
  (decreases l)
  = if n = 0 then ()
    else match l with
    | [] -> ()
    | _ :: tl -> lemma_drop_length_bound (n-1) tl

(** Lemma: when [n <= length l], [length (drop n l) = length l - n].
    Returns [int] because [nat - nat = int] in F*.
    @param n Number of elements to drop (must be ≤ |l|).
    @param l Input list.
    @returns Equality [|drop n l| == |l| - n] (as [int]). *)
let rec lemma_drop_length_exact (#a:Type) (n: nat) (l: list a) : Lemma
  (requires n <= List.Tot.length l)
  (ensures List.Tot.length (drop n l) = List.Tot.length l - n)
  (decreases l)
  = if n = 0 then ()
    else match l with
    | _ :: tl -> lemma_drop_length_exact (n-1) tl
