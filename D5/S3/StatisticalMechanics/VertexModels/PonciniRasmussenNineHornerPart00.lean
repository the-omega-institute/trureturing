/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart00
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart00
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; premises=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart00.step0,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart00.step1,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart00.step2,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart00.step3
   digest: Four split integer Horner steps for the nine-strand certificate. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PonciniRasmussenNineHorner = D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner

Direct frozen dependencies (declaration statement_ids):
none (direct prerequisites are unfrozen or pinned upstream)
step0_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_blocks
step0_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0_all
step0_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step0
step0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step1_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_blocks
step1_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1_all
step1_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step1
step1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step2_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_blocks
step2_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2_all
step2_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step2
step2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step3_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_blocks
step3_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3_all
step3_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step3
step3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
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
private theorem step0_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step0_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step0_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step0_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step0_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step0_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step0_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step0_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step0_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step0_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step0_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step0_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step0_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step0_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step0_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step0_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step0_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step0_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step0_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step0_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step0_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step0_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step0_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step0_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step0_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step0_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step0_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step0_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step0_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step0_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step0_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step0_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step0_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step0_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step0_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step0_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step0_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step0_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step0_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step0_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step0_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step0_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step0_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step0_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step0_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step0_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step0_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step0_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step0_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step0_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step0_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step0_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step0_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step0_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step0_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step0_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step0_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step0_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step0_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step0_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step0_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step0_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step0_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step0_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 0) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step0_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 0) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step0_part0 j
  · exact step0_part1 j
  · exact step0_part2 j
  · exact step0_part3 j
  · exact step0_part4 j
  · exact step0_part5 j
  · exact step0_part6 j
  · exact step0_part7 j
  · exact step0_part8 j
  · exact step0_part9 j
  · exact step0_part10 j
  · exact step0_part11 j
  · exact step0_part12 j
  · exact step0_part13 j
  · exact step0_part14 j
  · exact step0_part15 j
  · exact step0_part16 j
  · exact step0_part17 j
  · exact step0_part18 j
  · exact step0_part19 j
  · exact step0_part20 j
  · exact step0_part21 j
  · exact step0_part22 j
  · exact step0_part23 j
  · exact step0_part24 j
  · exact step0_part25 j
  · exact step0_part26 j
  · exact step0_part27 j
  · exact step0_part28 j
  · exact step0_part29 j
  · exact step0_part30 j
  · exact step0_part31 j
  · exact step0_part32 j
  · exact step0_part33 j
  · exact step0_part34 j
  · exact step0_part35 j
  · exact step0_part36 j
  · exact step0_part37 j
  · exact step0_part38 j
  · exact step0_part39 j
  · exact step0_part40 j
  · exact step0_part41 j
  · exact step0_part42 j
  · exact step0_part43 j
  · exact step0_part44 j
  · exact step0_part45 j
  · exact step0_part46 j
  · exact step0_part47 j
  · exact step0_part48 j
  · exact step0_part49 j
  · exact step0_part50 j
  · exact step0_part51 j
  · exact step0_part52 j
  · exact step0_part53 j
  · exact step0_part54 j
  · exact step0_part55 j
  · exact step0_part56 j
  · exact step0_part57 j
  · exact step0_part58 j
  · exact step0_part59 j
  · exact step0_part60 j
  · exact step0_part61 j
  · exact step0_part62 j
  · exact step0_part63 j
private theorem step0_all (i : Fin 8192) : (sparseHamiltonian (state 0) i + (if (i : Fin 8192).val == 4861 then (1 : Int) else 0)) = state 1 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step0_blocks b j
theorem step0 : (fun i => sparseHamiltonian (state 0) i + (if i.val == 4861 then (1 : Int) else 0)) = state 1 := funext step0_all
private theorem step1_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step1_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step1_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step1_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step1_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step1_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step1_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step1_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step1_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step1_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step1_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step1_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step1_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step1_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step1_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step1_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step1_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step1_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step1_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step1_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step1_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step1_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step1_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step1_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step1_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step1_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step1_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step1_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step1_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step1_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step1_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step1_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step1_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step1_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step1_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step1_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step1_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step1_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step1_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step1_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step1_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step1_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step1_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step1_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step1_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step1_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step1_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step1_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step1_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step1_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step1_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step1_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step1_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step1_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step1_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step1_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step1_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step1_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step1_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step1_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step1_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step1_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step1_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step1_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 1) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step1_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 1) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step1_part0 j
  · exact step1_part1 j
  · exact step1_part2 j
  · exact step1_part3 j
  · exact step1_part4 j
  · exact step1_part5 j
  · exact step1_part6 j
  · exact step1_part7 j
  · exact step1_part8 j
  · exact step1_part9 j
  · exact step1_part10 j
  · exact step1_part11 j
  · exact step1_part12 j
  · exact step1_part13 j
  · exact step1_part14 j
  · exact step1_part15 j
  · exact step1_part16 j
  · exact step1_part17 j
  · exact step1_part18 j
  · exact step1_part19 j
  · exact step1_part20 j
  · exact step1_part21 j
  · exact step1_part22 j
  · exact step1_part23 j
  · exact step1_part24 j
  · exact step1_part25 j
  · exact step1_part26 j
  · exact step1_part27 j
  · exact step1_part28 j
  · exact step1_part29 j
  · exact step1_part30 j
  · exact step1_part31 j
  · exact step1_part32 j
  · exact step1_part33 j
  · exact step1_part34 j
  · exact step1_part35 j
  · exact step1_part36 j
  · exact step1_part37 j
  · exact step1_part38 j
  · exact step1_part39 j
  · exact step1_part40 j
  · exact step1_part41 j
  · exact step1_part42 j
  · exact step1_part43 j
  · exact step1_part44 j
  · exact step1_part45 j
  · exact step1_part46 j
  · exact step1_part47 j
  · exact step1_part48 j
  · exact step1_part49 j
  · exact step1_part50 j
  · exact step1_part51 j
  · exact step1_part52 j
  · exact step1_part53 j
  · exact step1_part54 j
  · exact step1_part55 j
  · exact step1_part56 j
  · exact step1_part57 j
  · exact step1_part58 j
  · exact step1_part59 j
  · exact step1_part60 j
  · exact step1_part61 j
  · exact step1_part62 j
  · exact step1_part63 j
private theorem step1_all (i : Fin 8192) : (sparseHamiltonian (state 1) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 2 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step1_blocks b j
theorem step1 : (fun i => sparseHamiltonian (state 1) i + (if i.val == 4861 then (0 : Int) else 0)) = state 2 := funext step1_all
private theorem step2_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step2_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step2_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step2_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step2_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step2_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step2_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step2_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step2_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step2_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step2_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step2_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step2_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step2_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step2_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step2_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step2_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step2_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step2_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step2_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step2_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step2_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step2_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step2_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step2_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step2_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step2_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step2_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step2_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step2_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step2_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step2_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step2_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step2_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step2_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step2_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step2_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step2_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step2_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step2_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step2_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step2_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step2_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step2_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step2_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step2_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step2_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step2_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step2_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step2_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step2_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step2_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step2_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step2_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step2_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step2_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step2_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step2_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step2_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step2_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step2_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step2_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step2_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step2_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 2) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step2_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 2) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step2_part0 j
  · exact step2_part1 j
  · exact step2_part2 j
  · exact step2_part3 j
  · exact step2_part4 j
  · exact step2_part5 j
  · exact step2_part6 j
  · exact step2_part7 j
  · exact step2_part8 j
  · exact step2_part9 j
  · exact step2_part10 j
  · exact step2_part11 j
  · exact step2_part12 j
  · exact step2_part13 j
  · exact step2_part14 j
  · exact step2_part15 j
  · exact step2_part16 j
  · exact step2_part17 j
  · exact step2_part18 j
  · exact step2_part19 j
  · exact step2_part20 j
  · exact step2_part21 j
  · exact step2_part22 j
  · exact step2_part23 j
  · exact step2_part24 j
  · exact step2_part25 j
  · exact step2_part26 j
  · exact step2_part27 j
  · exact step2_part28 j
  · exact step2_part29 j
  · exact step2_part30 j
  · exact step2_part31 j
  · exact step2_part32 j
  · exact step2_part33 j
  · exact step2_part34 j
  · exact step2_part35 j
  · exact step2_part36 j
  · exact step2_part37 j
  · exact step2_part38 j
  · exact step2_part39 j
  · exact step2_part40 j
  · exact step2_part41 j
  · exact step2_part42 j
  · exact step2_part43 j
  · exact step2_part44 j
  · exact step2_part45 j
  · exact step2_part46 j
  · exact step2_part47 j
  · exact step2_part48 j
  · exact step2_part49 j
  · exact step2_part50 j
  · exact step2_part51 j
  · exact step2_part52 j
  · exact step2_part53 j
  · exact step2_part54 j
  · exact step2_part55 j
  · exact step2_part56 j
  · exact step2_part57 j
  · exact step2_part58 j
  · exact step2_part59 j
  · exact step2_part60 j
  · exact step2_part61 j
  · exact step2_part62 j
  · exact step2_part63 j
private theorem step2_all (i : Fin 8192) : (sparseHamiltonian (state 2) i + (if (i : Fin 8192).val == 4861 then (-163 : Int) else 0)) = state 3 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step2_blocks b j
theorem step2 : (fun i => sparseHamiltonian (state 2) i + (if i.val == 4861 then (-163 : Int) else 0)) = state 3 := funext step2_all
private theorem step3_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step3_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step3_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step3_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step3_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step3_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step3_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step3_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step3_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step3_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step3_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step3_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step3_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step3_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step3_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step3_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step3_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step3_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step3_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step3_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step3_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step3_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step3_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step3_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step3_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step3_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step3_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step3_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step3_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step3_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step3_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step3_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step3_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step3_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step3_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step3_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step3_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step3_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step3_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step3_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step3_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step3_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step3_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step3_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step3_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step3_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step3_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step3_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step3_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step3_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step3_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step3_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step3_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step3_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step3_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step3_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step3_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step3_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step3_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step3_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step3_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step3_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step3_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step3_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 3) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step3_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 3) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step3_part0 j
  · exact step3_part1 j
  · exact step3_part2 j
  · exact step3_part3 j
  · exact step3_part4 j
  · exact step3_part5 j
  · exact step3_part6 j
  · exact step3_part7 j
  · exact step3_part8 j
  · exact step3_part9 j
  · exact step3_part10 j
  · exact step3_part11 j
  · exact step3_part12 j
  · exact step3_part13 j
  · exact step3_part14 j
  · exact step3_part15 j
  · exact step3_part16 j
  · exact step3_part17 j
  · exact step3_part18 j
  · exact step3_part19 j
  · exact step3_part20 j
  · exact step3_part21 j
  · exact step3_part22 j
  · exact step3_part23 j
  · exact step3_part24 j
  · exact step3_part25 j
  · exact step3_part26 j
  · exact step3_part27 j
  · exact step3_part28 j
  · exact step3_part29 j
  · exact step3_part30 j
  · exact step3_part31 j
  · exact step3_part32 j
  · exact step3_part33 j
  · exact step3_part34 j
  · exact step3_part35 j
  · exact step3_part36 j
  · exact step3_part37 j
  · exact step3_part38 j
  · exact step3_part39 j
  · exact step3_part40 j
  · exact step3_part41 j
  · exact step3_part42 j
  · exact step3_part43 j
  · exact step3_part44 j
  · exact step3_part45 j
  · exact step3_part46 j
  · exact step3_part47 j
  · exact step3_part48 j
  · exact step3_part49 j
  · exact step3_part50 j
  · exact step3_part51 j
  · exact step3_part52 j
  · exact step3_part53 j
  · exact step3_part54 j
  · exact step3_part55 j
  · exact step3_part56 j
  · exact step3_part57 j
  · exact step3_part58 j
  · exact step3_part59 j
  · exact step3_part60 j
  · exact step3_part61 j
  · exact step3_part62 j
  · exact step3_part63 j
private theorem step3_all (i : Fin 8192) : (sparseHamiltonian (state 3) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 4 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step3_blocks b j
theorem step3 : (fun i => sparseHamiltonian (state 3) i + (if i.val == 4861 then (0 : Int) else 0)) = state 4 := funext step3_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
