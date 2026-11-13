/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; premises=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step20,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step21,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step22,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step23
   digest: Four split integer Horner steps for the nine-strand certificate. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PonciniRasmussenNineHorner = D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner

Direct frozen dependencies (declaration statement_ids):
none (direct prerequisites are unfrozen or pinned upstream)
step20_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_blocks
step20_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20_all
step20_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step20
step20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step21_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_blocks
step21_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21_all
step21_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step21
step21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step22_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_blocks
step22_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22_all
step22_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step22
step22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step23_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_blocks
step23_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23_all
step23_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step23
step23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
-/
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineHornerData
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Exact integer data and finite kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
private theorem step20_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step20_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step20_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step20_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step20_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step20_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step20_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step20_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step20_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step20_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step20_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step20_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step20_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step20_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step20_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step20_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step20_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step20_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step20_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step20_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step20_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step20_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step20_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step20_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step20_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step20_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step20_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step20_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step20_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step20_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step20_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step20_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step20_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step20_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step20_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step20_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step20_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step20_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step20_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step20_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step20_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step20_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step20_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step20_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step20_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step20_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step20_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step20_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step20_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step20_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step20_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step20_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step20_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step20_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step20_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step20_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step20_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step20_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step20_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step20_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step20_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step20_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step20_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step20_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 20) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step20_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 20) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step20_part0 j
  · exact step20_part1 j
  · exact step20_part2 j
  · exact step20_part3 j
  · exact step20_part4 j
  · exact step20_part5 j
  · exact step20_part6 j
  · exact step20_part7 j
  · exact step20_part8 j
  · exact step20_part9 j
  · exact step20_part10 j
  · exact step20_part11 j
  · exact step20_part12 j
  · exact step20_part13 j
  · exact step20_part14 j
  · exact step20_part15 j
  · exact step20_part16 j
  · exact step20_part17 j
  · exact step20_part18 j
  · exact step20_part19 j
  · exact step20_part20 j
  · exact step20_part21 j
  · exact step20_part22 j
  · exact step20_part23 j
  · exact step20_part24 j
  · exact step20_part25 j
  · exact step20_part26 j
  · exact step20_part27 j
  · exact step20_part28 j
  · exact step20_part29 j
  · exact step20_part30 j
  · exact step20_part31 j
  · exact step20_part32 j
  · exact step20_part33 j
  · exact step20_part34 j
  · exact step20_part35 j
  · exact step20_part36 j
  · exact step20_part37 j
  · exact step20_part38 j
  · exact step20_part39 j
  · exact step20_part40 j
  · exact step20_part41 j
  · exact step20_part42 j
  · exact step20_part43 j
  · exact step20_part44 j
  · exact step20_part45 j
  · exact step20_part46 j
  · exact step20_part47 j
  · exact step20_part48 j
  · exact step20_part49 j
  · exact step20_part50 j
  · exact step20_part51 j
  · exact step20_part52 j
  · exact step20_part53 j
  · exact step20_part54 j
  · exact step20_part55 j
  · exact step20_part56 j
  · exact step20_part57 j
  · exact step20_part58 j
  · exact step20_part59 j
  · exact step20_part60 j
  · exact step20_part61 j
  · exact step20_part62 j
  · exact step20_part63 j
private theorem step20_all (i : Fin 8192) : (sparseHamiltonian (state 20) i + (if (i : Fin 8192).val == 4861 then (76659122475479 : Int) else 0)) = state 21 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step20_blocks b j
theorem step20 : (fun i => sparseHamiltonian (state 20) i + (if i.val == 4861 then (76659122475479 : Int) else 0)) = state 21 := funext step20_all
private theorem step21_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step21_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step21_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step21_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step21_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step21_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step21_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step21_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step21_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step21_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step21_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step21_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step21_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step21_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step21_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step21_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step21_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step21_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step21_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step21_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step21_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step21_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step21_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step21_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step21_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step21_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step21_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step21_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step21_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step21_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step21_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step21_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step21_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step21_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step21_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step21_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step21_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step21_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step21_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step21_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step21_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step21_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step21_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step21_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step21_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step21_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step21_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step21_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step21_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step21_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step21_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step21_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step21_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step21_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step21_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step21_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step21_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step21_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step21_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step21_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step21_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step21_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step21_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step21_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 21) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step21_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 21) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step21_part0 j
  · exact step21_part1 j
  · exact step21_part2 j
  · exact step21_part3 j
  · exact step21_part4 j
  · exact step21_part5 j
  · exact step21_part6 j
  · exact step21_part7 j
  · exact step21_part8 j
  · exact step21_part9 j
  · exact step21_part10 j
  · exact step21_part11 j
  · exact step21_part12 j
  · exact step21_part13 j
  · exact step21_part14 j
  · exact step21_part15 j
  · exact step21_part16 j
  · exact step21_part17 j
  · exact step21_part18 j
  · exact step21_part19 j
  · exact step21_part20 j
  · exact step21_part21 j
  · exact step21_part22 j
  · exact step21_part23 j
  · exact step21_part24 j
  · exact step21_part25 j
  · exact step21_part26 j
  · exact step21_part27 j
  · exact step21_part28 j
  · exact step21_part29 j
  · exact step21_part30 j
  · exact step21_part31 j
  · exact step21_part32 j
  · exact step21_part33 j
  · exact step21_part34 j
  · exact step21_part35 j
  · exact step21_part36 j
  · exact step21_part37 j
  · exact step21_part38 j
  · exact step21_part39 j
  · exact step21_part40 j
  · exact step21_part41 j
  · exact step21_part42 j
  · exact step21_part43 j
  · exact step21_part44 j
  · exact step21_part45 j
  · exact step21_part46 j
  · exact step21_part47 j
  · exact step21_part48 j
  · exact step21_part49 j
  · exact step21_part50 j
  · exact step21_part51 j
  · exact step21_part52 j
  · exact step21_part53 j
  · exact step21_part54 j
  · exact step21_part55 j
  · exact step21_part56 j
  · exact step21_part57 j
  · exact step21_part58 j
  · exact step21_part59 j
  · exact step21_part60 j
  · exact step21_part61 j
  · exact step21_part62 j
  · exact step21_part63 j
private theorem step21_all (i : Fin 8192) : (sparseHamiltonian (state 21) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 22 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step21_blocks b j
theorem step21 : (fun i => sparseHamiltonian (state 21) i + (if i.val == 4861 then (0 : Int) else 0)) = state 22 := funext step21_all
private theorem step22_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step22_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step22_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step22_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step22_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step22_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step22_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step22_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step22_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step22_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step22_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step22_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step22_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step22_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step22_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step22_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step22_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step22_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step22_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step22_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step22_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step22_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step22_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step22_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step22_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step22_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step22_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step22_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step22_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step22_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step22_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step22_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step22_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step22_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step22_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step22_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step22_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step22_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step22_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step22_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step22_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step22_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step22_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step22_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step22_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step22_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step22_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step22_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step22_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step22_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step22_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step22_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step22_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step22_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step22_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step22_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step22_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step22_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step22_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step22_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step22_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step22_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step22_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step22_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 22) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step22_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 22) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step22_part0 j
  · exact step22_part1 j
  · exact step22_part2 j
  · exact step22_part3 j
  · exact step22_part4 j
  · exact step22_part5 j
  · exact step22_part6 j
  · exact step22_part7 j
  · exact step22_part8 j
  · exact step22_part9 j
  · exact step22_part10 j
  · exact step22_part11 j
  · exact step22_part12 j
  · exact step22_part13 j
  · exact step22_part14 j
  · exact step22_part15 j
  · exact step22_part16 j
  · exact step22_part17 j
  · exact step22_part18 j
  · exact step22_part19 j
  · exact step22_part20 j
  · exact step22_part21 j
  · exact step22_part22 j
  · exact step22_part23 j
  · exact step22_part24 j
  · exact step22_part25 j
  · exact step22_part26 j
  · exact step22_part27 j
  · exact step22_part28 j
  · exact step22_part29 j
  · exact step22_part30 j
  · exact step22_part31 j
  · exact step22_part32 j
  · exact step22_part33 j
  · exact step22_part34 j
  · exact step22_part35 j
  · exact step22_part36 j
  · exact step22_part37 j
  · exact step22_part38 j
  · exact step22_part39 j
  · exact step22_part40 j
  · exact step22_part41 j
  · exact step22_part42 j
  · exact step22_part43 j
  · exact step22_part44 j
  · exact step22_part45 j
  · exact step22_part46 j
  · exact step22_part47 j
  · exact step22_part48 j
  · exact step22_part49 j
  · exact step22_part50 j
  · exact step22_part51 j
  · exact step22_part52 j
  · exact step22_part53 j
  · exact step22_part54 j
  · exact step22_part55 j
  · exact step22_part56 j
  · exact step22_part57 j
  · exact step22_part58 j
  · exact step22_part59 j
  · exact step22_part60 j
  · exact step22_part61 j
  · exact step22_part62 j
  · exact step22_part63 j
private theorem step22_all (i : Fin 8192) : (sparseHamiltonian (state 22) i + (if (i : Fin 8192).val == 4861 then (-450854928573687 : Int) else 0)) = state 23 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step22_blocks b j
theorem step22 : (fun i => sparseHamiltonian (state 22) i + (if i.val == 4861 then (-450854928573687 : Int) else 0)) = state 23 := funext step22_all
private theorem step23_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step23_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step23_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step23_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step23_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step23_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step23_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step23_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step23_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step23_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step23_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step23_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step23_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step23_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step23_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step23_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step23_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step23_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step23_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step23_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step23_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step23_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step23_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step23_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step23_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step23_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step23_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step23_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step23_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step23_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step23_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step23_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step23_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step23_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step23_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step23_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step23_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step23_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step23_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step23_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step23_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step23_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step23_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step23_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step23_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step23_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step23_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step23_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step23_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step23_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step23_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step23_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step23_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step23_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step23_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step23_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step23_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step23_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step23_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step23_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step23_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step23_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step23_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step23_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 23) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step23_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 23) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step23_part0 j
  · exact step23_part1 j
  · exact step23_part2 j
  · exact step23_part3 j
  · exact step23_part4 j
  · exact step23_part5 j
  · exact step23_part6 j
  · exact step23_part7 j
  · exact step23_part8 j
  · exact step23_part9 j
  · exact step23_part10 j
  · exact step23_part11 j
  · exact step23_part12 j
  · exact step23_part13 j
  · exact step23_part14 j
  · exact step23_part15 j
  · exact step23_part16 j
  · exact step23_part17 j
  · exact step23_part18 j
  · exact step23_part19 j
  · exact step23_part20 j
  · exact step23_part21 j
  · exact step23_part22 j
  · exact step23_part23 j
  · exact step23_part24 j
  · exact step23_part25 j
  · exact step23_part26 j
  · exact step23_part27 j
  · exact step23_part28 j
  · exact step23_part29 j
  · exact step23_part30 j
  · exact step23_part31 j
  · exact step23_part32 j
  · exact step23_part33 j
  · exact step23_part34 j
  · exact step23_part35 j
  · exact step23_part36 j
  · exact step23_part37 j
  · exact step23_part38 j
  · exact step23_part39 j
  · exact step23_part40 j
  · exact step23_part41 j
  · exact step23_part42 j
  · exact step23_part43 j
  · exact step23_part44 j
  · exact step23_part45 j
  · exact step23_part46 j
  · exact step23_part47 j
  · exact step23_part48 j
  · exact step23_part49 j
  · exact step23_part50 j
  · exact step23_part51 j
  · exact step23_part52 j
  · exact step23_part53 j
  · exact step23_part54 j
  · exact step23_part55 j
  · exact step23_part56 j
  · exact step23_part57 j
  · exact step23_part58 j
  · exact step23_part59 j
  · exact step23_part60 j
  · exact step23_part61 j
  · exact step23_part62 j
  · exact step23_part63 j
private theorem step23_all (i : Fin 8192) : (sparseHamiltonian (state 23) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 24 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step23_blocks b j
theorem step23 : (fun i => sparseHamiltonian (state 23) i + (if i.val == 4861 then (0 : Int) else 0)) = state 24 := funext step23_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
