(*
  This file is part of the verified smart contract project of SECBIT Labs.

  Copyright 2018 SECBIT Labs

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public License
  as published by the Free Software Foundation, either version 3 of
  the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import
        Nat
        List
        ZArith
        Coq.FSets.FMapWeakList
        Coq.Structures.DecidableType
        Coq.Structures.DecidableTypeEx.
Require Import
        Types.

Set Implicit Arguments.
Unset Strict Implicit.


(** Abstract Mapping Element Type *)
Module Type ElemType.
  Parameter Inline elt: Type.
  Parameter Inline elt_zero: elt.
  Parameter Inline elt_eq: elt -> elt -> Prop.

  Axiom elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.

  Axiom elt_eq_refl:
    forall x: elt, elt_eq x x.

  Axiom elt_eq_symm:
    forall (x y: elt), elt_eq x y -> elt_eq y x.

  Axiom elt_eq_trans:
    forall (x y: elt), elt_eq x y -> forall (z: elt), elt_eq y z -> elt_eq x z.
End ElemType.


(** Abstract Mapping Type *)
Module Mapping (K: DecidableType) (Elt: ElemType).
  Module Import map := FMapWeakList.Make(K).
  Module Import et := Elt.

  Notation t := (map.t elt).
  Notation empty := (map.empty elt).

  Definition get (m: t) (k: K.t) : elt :=
    match find k m with
    | Some v => v
    | None => elt_zero
    end.

  Definition upd (m: t) (k: K.t) (v: elt) : t := add k v m.

  Definition equal (m m': t) := forall k, get m k = get m' k.
End Mapping.


(** Decidable Types *)
Module Address_as_DT <: UsualDecidableType := Nat_as_DT.
Module AA_as_DT := DecidableTypeEx.PairDecidableType (Address_as_DT) (Address_as_DT).
Module Hash_as_DT <: UsualDecidableType := Nat_as_DT.
Module AH_as_DT := DecidableTypeEx.PairDecidableType (Address_as_DT) (Hash_as_DT).
Module AAH_as_DT := DecidableTypeEx.PairDecidableType (AA_as_DT) (Hash_as_DT).


(** Concrete Element Types *)
Module ValElem <: ElemType.
  Definition elt : Type := value.
  Definition elt_zero := 0.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    exact Nat.eq_dec.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    unfold elt_eq; intros; congruence.
  Qed.
End ValElem.

Module BoolElem <: ElemType.
  Definition elt : Type := bool.
  Definition elt_zero := false.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    exact Bool.bool_dec.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    unfold elt_eq; intros; congruence.
  Qed.
End BoolElem.


(** Concrete Mapping Types *)
(* Address -> Nat *)
Module A2V := Mapping Address_as_DT ValElem.
(* (Address, Address) -> Nat *)
Module AA2V := Mapping AA_as_DT ValElem.
(* bytes20 -> Nat *)
Module H2V := Mapping Hash_as_DT ValElem.
(* address -> bytes20 -> bool *)
Module AH2B := Mapping AH_as_DT BoolElem.
(* address -> bytes20 -> Nat *)
Module AH2V := Mapping AH_as_DT ValElem.
(* address -> address -> bytes20 -> Nat *)
Module AAH2V := Mapping AAH_as_DT ValElem.


(** Shortcuts for map updates  *)
Definition AA2V_upd_inc (m: AA2V.t) (a0 a1: address) (v: value) : AA2V.t :=
  AA2V.upd m (a0, a1) (plus_with_overflow (AA2V.get m (a0, a1)) v).

Definition AA2V_upd_dec (m: AA2V.t) (a0 a1: address) (v: value) : AA2V.t :=
  AA2V.upd m (a0, a1) (minus_with_underflow (AA2V.get m (a0, a1)) v).
