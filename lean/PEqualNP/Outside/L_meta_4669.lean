import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4669_aux

abbrev Signal := Fin 24 → Bool

def sample (r : Fin 24) (i : Fin 9) : Bool :=
  ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288, 42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ).getD r.val 0 |>.testBit i.val

def input (r : Fin 24) : List Bool :=
  List.ofFn (sample r) ++ [!sample r 0, sample r 2 || sample r 8]

def base : List Signal :=
  List.ofFn (fun (i : Fin 11) (r : Fin 24) => (input r).getD i.val false) ++
    [fun _ => false, fun _ => true]

def w13 (r : Fin 24) : Bool := (base.getD 6 (fun _ => false)) r || (base.getD 8 (fun _ => false)) r
def w14 (r : Fin 24) : Bool := (base.getD 3 (fun _ => false)) r && (base.getD 9 (fun _ => false)) r
def w15 (r : Fin 24) : Bool := (base.getD 0 (fun _ => false)) r && (base.getD 10 (fun _ => false)) r
def w16 (r : Fin 24) : Bool := (base.getD 3 (fun _ => false)) r && (base.getD 10 (fun _ => false)) r
def w17 (r : Fin 24) : Bool := (base.getD 1 (fun _ => false)) r || w13 r
def w18 (r : Fin 24) : Bool := (base.getD 3 (fun _ => false)) r || w15 r
def w19 (r : Fin 24) : Bool := w13 r && w16 r
def w20 (r : Fin 24) : Bool := w14 r && w16 r
def w21 (r : Fin 24) : Bool := (base.getD 4 (fun _ => false)) r || w18 r
def w22 (r : Fin 24) : Bool := w17 r && w21 r
def w23 (r : Fin 24) : Bool := !(w22 r)
def w24 (r : Fin 24) : Bool := w19 r || w23 r
def w25 (r : Fin 24) : Bool := w20 r || w24 r

def result : List Signal := [w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25]

lemma last_target : w25 = (fun r : Fin 24 => decide (r.val < 12)) := by
  funext r
  fin_cases r <;> decide

end PEqualNP.Outside.L_meta_4669_aux

open PEqualNP.Outside.L_meta_4669_aux

theorem PEqualNP.Outside.L_meta_4669 : ¬ (∀ x1 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)],   have x3 : Fin (24 : ℕ) → Fin (9 : ℕ) → Bool := fun (x3 : Fin (24 : ℕ)) (x4 : Fin (9 : ℕ)) => ([(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x4;   have x4 : Fin (24 : ℕ) → List Bool := fun (x4 : Fin (24 : ℕ)) => List.ofFn (x3 x4) ++ [!x3 x4 (0 : Fin (9 : ℕ)), x3 x4 (Fin.ofNat (9 : ℕ) (x1 / (10 : ℕ))) || x3 x4 (Fin.ofNat (9 : ℕ) (x1 % (10 : ℕ)))];   have x5 : List (Fin (24 : ℕ) → Bool) := (List.ofFn fun (x5 : Fin (11 : ℕ)) (x6 : Fin (24 : ℕ)) => (x4 x6).getD (↑x5) Bool.false) ++ [fun (x5 : Fin (24 : ℕ)) => Bool.false, fun (x5 : Fin (24 : ℕ)) => Bool.true];   ∀ (x6 : List (Fin (24 : ℕ) → Bool)),     x6.length ≤ (13 : ℕ) →       (∀ (x8 : Fin x6.length),           have x9 : List (Fin (24 : ℕ) → Bool) := x5 ++ List.take (↑x8) x6;           (∃ x10 ∈ x9, x6.get x8 = fun (x11 : Fin (24 : ℕ)) => !x10 x11) ∨ ∃ x10 ∈ x9, ∃ x11 ∈ x9, (x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 && x11 x12) ∨ x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 || x11 x12) →         (fun (x9 : Fin (24 : ℕ)) => Decidable.decide (↑x9 < (12 : ℕ))) ∉ x5 ++ x6) := by
  intro all
  have h := all 28 (by decide)
  dsimp only at h
  change ∀ (xs : List Signal), xs.length ≤ 13 →
    (∀ i : Fin xs.length,
      (∃ x ∈ base ++ xs.take i.val, xs.get i = fun r => !x r) ∨
      ∃ x ∈ base ++ xs.take i.val, ∃ y ∈ base ++ xs.take i.val,
        (xs.get i = fun r => x r && y r) ∨ (xs.get i = fun r => x r || y r)) →
    (fun r : Fin 24 => decide (r.val < 12)) ∉ base ++ xs at h
  apply (h result (by decide) ?_)
  rw [← last_target]
  exact List.mem_append.mpr (Or.inr (by simp [result]))
  intro i
  fin_cases i
  · exact Or.inr ⟨(base.getD 6 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨6, by decide, rfl⟩, (base.getD 8 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨8, by decide, rfl⟩, Or.inr rfl⟩
  · exact Or.inr ⟨(base.getD 3 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨3, by decide, rfl⟩, (base.getD 9 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨9, by decide, rfl⟩, Or.inl rfl⟩
  · exact Or.inr ⟨(base.getD 0 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, (base.getD 10 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨10, by decide, rfl⟩, Or.inl rfl⟩
  · exact Or.inr ⟨(base.getD 3 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨3, by decide, rfl⟩, (base.getD 10 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨10, by decide, rfl⟩, Or.inl rfl⟩
  · exact Or.inr ⟨(base.getD 1 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, w13, by exact List.mem_iff_getElem.mpr ⟨13, by decide, rfl⟩, Or.inr rfl⟩
  · exact Or.inr ⟨(base.getD 3 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨3, by decide, rfl⟩, w15, by exact List.mem_iff_getElem.mpr ⟨15, by decide, rfl⟩, Or.inr rfl⟩
  · exact Or.inr ⟨w13, by exact List.mem_iff_getElem.mpr ⟨13, by decide, rfl⟩, w16, by exact List.mem_iff_getElem.mpr ⟨16, by decide, rfl⟩, Or.inl rfl⟩
  · exact Or.inr ⟨w14, by exact List.mem_iff_getElem.mpr ⟨14, by decide, rfl⟩, w16, by exact List.mem_iff_getElem.mpr ⟨16, by decide, rfl⟩, Or.inl rfl⟩
  · exact Or.inr ⟨(base.getD 4 (fun _ => false)), by exact List.mem_iff_getElem.mpr ⟨4, by decide, rfl⟩, w18, by exact List.mem_iff_getElem.mpr ⟨18, by decide, rfl⟩, Or.inr rfl⟩
  · exact Or.inr ⟨w17, by exact List.mem_iff_getElem.mpr ⟨17, by decide, rfl⟩, w21, by exact List.mem_iff_getElem.mpr ⟨21, by decide, rfl⟩, Or.inl rfl⟩
  · exact Or.inl ⟨w22, by exact List.mem_iff_getElem.mpr ⟨22, by decide, rfl⟩, rfl⟩
  · exact Or.inr ⟨w19, by exact List.mem_iff_getElem.mpr ⟨19, by decide, rfl⟩, w23, by exact List.mem_iff_getElem.mpr ⟨23, by decide, rfl⟩, Or.inr rfl⟩
  · exact Or.inr ⟨w20, by exact List.mem_iff_getElem.mpr ⟨20, by decide, rfl⟩, w24, by exact List.mem_iff_getElem.mpr ⟨24, by decide, rfl⟩, Or.inr rfl⟩
