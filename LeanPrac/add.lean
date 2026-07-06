def myle (m n : Nat) : Prop := ∃ j : Nat, m + j = n

theorem question_e (m n k : Nat) (h : myle m n) : myle (m + k) (n + k) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  calc
    (m + k) + j = m + (k + j) := by rw [Nat.add_assoc]
    _ = m + (j + k) := by rw [Nat.add_comm k j]
    _ = (m + j) + k := by rw [← Nat.add_assoc]
    _ = n + k := by rw [hj]
