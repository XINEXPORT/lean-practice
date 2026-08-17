import Mathlib.Tactic
open Set Function

example {A B : Type*} {f : A → B} (hf : Bijective f) (S : Set A) :
    f '' Sᶜ = (f '' S)ᶜ := by
  obtain ⟨hinj, hsurj⟩ := hf
  ext y
  constructor
-- (⊆) image of complement ⊆ complement of image (prove injective)
  rintro ⟨x, hx, rfl⟩ s hs hfs
  exact hx (hinj hfs ▸ hs)
-- (⊇) complement of image ⊆ image of complement (prove surjective)
  intro hy
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨x, fun hx => hy x hx rfl, rfl⟩
