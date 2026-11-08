/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart13
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart13
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; premises=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart13.step52,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart13.step53,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart13.step54,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart13.step55
   digest: Four split integer Horner steps for the nine-strand certificate. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PonciniRasmussenNineHorner = D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner

Direct frozen dependencies (declaration statement_ids):
none (direct prerequisites are unfrozen or pinned upstream)
step52_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_blocks
step52_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52_all
step52_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step52
step52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step53_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_blocks
step53_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53_all
step53_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step53
step53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step54_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_blocks
step54_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54_all
step54_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step54
step54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
step55_part0: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part1: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part2: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part3: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part4: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part5: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part6: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part7: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part8: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part9: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part10: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part11: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part12: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part13: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part14: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part15: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part16: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part17: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part18: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part19: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part20: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part21: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part22: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part23: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part24: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part25: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part26: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part27: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part28: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part29: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part30: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part31: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part32: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part33: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part34: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part35: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part36: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part37: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part38: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part39: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part40: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part41: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part42: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part43: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part44: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part45: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part46: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part47: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part48: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part49: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part50: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part51: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part52: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part53: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part54: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part56: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part57: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part58: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part59: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part60: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part61: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part62: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_part63: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_blocks
step55_blocks: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55_all
step55_all: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.step55
step55: proof_shape=bind-only; consumers=PonciniRasmussenNineHorner.annihilation
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
private theorem step52_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step52_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step52_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step52_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step52_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step52_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step52_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step52_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step52_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step52_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step52_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step52_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step52_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step52_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step52_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step52_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step52_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step52_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step52_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step52_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step52_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step52_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step52_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step52_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step52_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step52_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step52_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step52_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step52_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step52_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step52_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step52_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step52_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step52_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step52_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step52_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step52_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step52_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step52_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step52_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step52_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step52_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step52_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step52_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step52_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step52_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step52_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step52_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step52_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step52_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step52_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step52_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step52_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step52_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step52_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step52_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step52_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step52_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step52_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step52_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step52_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step52_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step52_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step52_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 52) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step52_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 52) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step52_part0 j
  · exact step52_part1 j
  · exact step52_part2 j
  · exact step52_part3 j
  · exact step52_part4 j
  · exact step52_part5 j
  · exact step52_part6 j
  · exact step52_part7 j
  · exact step52_part8 j
  · exact step52_part9 j
  · exact step52_part10 j
  · exact step52_part11 j
  · exact step52_part12 j
  · exact step52_part13 j
  · exact step52_part14 j
  · exact step52_part15 j
  · exact step52_part16 j
  · exact step52_part17 j
  · exact step52_part18 j
  · exact step52_part19 j
  · exact step52_part20 j
  · exact step52_part21 j
  · exact step52_part22 j
  · exact step52_part23 j
  · exact step52_part24 j
  · exact step52_part25 j
  · exact step52_part26 j
  · exact step52_part27 j
  · exact step52_part28 j
  · exact step52_part29 j
  · exact step52_part30 j
  · exact step52_part31 j
  · exact step52_part32 j
  · exact step52_part33 j
  · exact step52_part34 j
  · exact step52_part35 j
  · exact step52_part36 j
  · exact step52_part37 j
  · exact step52_part38 j
  · exact step52_part39 j
  · exact step52_part40 j
  · exact step52_part41 j
  · exact step52_part42 j
  · exact step52_part43 j
  · exact step52_part44 j
  · exact step52_part45 j
  · exact step52_part46 j
  · exact step52_part47 j
  · exact step52_part48 j
  · exact step52_part49 j
  · exact step52_part50 j
  · exact step52_part51 j
  · exact step52_part52 j
  · exact step52_part53 j
  · exact step52_part54 j
  · exact step52_part55 j
  · exact step52_part56 j
  · exact step52_part57 j
  · exact step52_part58 j
  · exact step52_part59 j
  · exact step52_part60 j
  · exact step52_part61 j
  · exact step52_part62 j
  · exact step52_part63 j
private theorem step52_all (i : Fin 8192) : (sparseHamiltonian (state 52) i + (if (i : Fin 8192).val == 4861 then (64282035899880 : Int) else 0)) = state 53 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step52_blocks b j
theorem step52 : (fun i => sparseHamiltonian (state 52) i + (if i.val == 4861 then (64282035899880 : Int) else 0)) = state 53 := funext step52_all
private theorem step53_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step53_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step53_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step53_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step53_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step53_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step53_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step53_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step53_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step53_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step53_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step53_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step53_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step53_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step53_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step53_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step53_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step53_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step53_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step53_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step53_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step53_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step53_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step53_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step53_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step53_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step53_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step53_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step53_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step53_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step53_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step53_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step53_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step53_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step53_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step53_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step53_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step53_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step53_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step53_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step53_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step53_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step53_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step53_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step53_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step53_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step53_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step53_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step53_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step53_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step53_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step53_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step53_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step53_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step53_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step53_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step53_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step53_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step53_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step53_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step53_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step53_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step53_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step53_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 53) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step53_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 53) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step53_part0 j
  · exact step53_part1 j
  · exact step53_part2 j
  · exact step53_part3 j
  · exact step53_part4 j
  · exact step53_part5 j
  · exact step53_part6 j
  · exact step53_part7 j
  · exact step53_part8 j
  · exact step53_part9 j
  · exact step53_part10 j
  · exact step53_part11 j
  · exact step53_part12 j
  · exact step53_part13 j
  · exact step53_part14 j
  · exact step53_part15 j
  · exact step53_part16 j
  · exact step53_part17 j
  · exact step53_part18 j
  · exact step53_part19 j
  · exact step53_part20 j
  · exact step53_part21 j
  · exact step53_part22 j
  · exact step53_part23 j
  · exact step53_part24 j
  · exact step53_part25 j
  · exact step53_part26 j
  · exact step53_part27 j
  · exact step53_part28 j
  · exact step53_part29 j
  · exact step53_part30 j
  · exact step53_part31 j
  · exact step53_part32 j
  · exact step53_part33 j
  · exact step53_part34 j
  · exact step53_part35 j
  · exact step53_part36 j
  · exact step53_part37 j
  · exact step53_part38 j
  · exact step53_part39 j
  · exact step53_part40 j
  · exact step53_part41 j
  · exact step53_part42 j
  · exact step53_part43 j
  · exact step53_part44 j
  · exact step53_part45 j
  · exact step53_part46 j
  · exact step53_part47 j
  · exact step53_part48 j
  · exact step53_part49 j
  · exact step53_part50 j
  · exact step53_part51 j
  · exact step53_part52 j
  · exact step53_part53 j
  · exact step53_part54 j
  · exact step53_part55 j
  · exact step53_part56 j
  · exact step53_part57 j
  · exact step53_part58 j
  · exact step53_part59 j
  · exact step53_part60 j
  · exact step53_part61 j
  · exact step53_part62 j
  · exact step53_part63 j
private theorem step53_all (i : Fin 8192) : (sparseHamiltonian (state 53) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 54 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step53_blocks b j
theorem step53 : (fun i => sparseHamiltonian (state 53) i + (if i.val == 4861 then (0 : Int) else 0)) = state 54 := funext step53_all
private theorem step54_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step54_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step54_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step54_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step54_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step54_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step54_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step54_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step54_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step54_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step54_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step54_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step54_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step54_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step54_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step54_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step54_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step54_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step54_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step54_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step54_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step54_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step54_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step54_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step54_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step54_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step54_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step54_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step54_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step54_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step54_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step54_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step54_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step54_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step54_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step54_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step54_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step54_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step54_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step54_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step54_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step54_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step54_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step54_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step54_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step54_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step54_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step54_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step54_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step54_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step54_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step54_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step54_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step54_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step54_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step54_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step54_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step54_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step54_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step54_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step54_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step54_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step54_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step54_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 54) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step54_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 54) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step54_part0 j
  · exact step54_part1 j
  · exact step54_part2 j
  · exact step54_part3 j
  · exact step54_part4 j
  · exact step54_part5 j
  · exact step54_part6 j
  · exact step54_part7 j
  · exact step54_part8 j
  · exact step54_part9 j
  · exact step54_part10 j
  · exact step54_part11 j
  · exact step54_part12 j
  · exact step54_part13 j
  · exact step54_part14 j
  · exact step54_part15 j
  · exact step54_part16 j
  · exact step54_part17 j
  · exact step54_part18 j
  · exact step54_part19 j
  · exact step54_part20 j
  · exact step54_part21 j
  · exact step54_part22 j
  · exact step54_part23 j
  · exact step54_part24 j
  · exact step54_part25 j
  · exact step54_part26 j
  · exact step54_part27 j
  · exact step54_part28 j
  · exact step54_part29 j
  · exact step54_part30 j
  · exact step54_part31 j
  · exact step54_part32 j
  · exact step54_part33 j
  · exact step54_part34 j
  · exact step54_part35 j
  · exact step54_part36 j
  · exact step54_part37 j
  · exact step54_part38 j
  · exact step54_part39 j
  · exact step54_part40 j
  · exact step54_part41 j
  · exact step54_part42 j
  · exact step54_part43 j
  · exact step54_part44 j
  · exact step54_part45 j
  · exact step54_part46 j
  · exact step54_part47 j
  · exact step54_part48 j
  · exact step54_part49 j
  · exact step54_part50 j
  · exact step54_part51 j
  · exact step54_part52 j
  · exact step54_part53 j
  · exact step54_part54 j
  · exact step54_part55 j
  · exact step54_part56 j
  · exact step54_part57 j
  · exact step54_part58 j
  · exact step54_part59 j
  · exact step54_part60 j
  · exact step54_part61 j
  · exact step54_part62 j
  · exact step54_part63 j
private theorem step54_all (i : Fin 8192) : (sparseHamiltonian (state 54) i + (if (i : Fin 8192).val == 4861 then (-2771640702288 : Int) else 0)) = state 55 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step54_blocks b j
theorem step54 : (fun i => sparseHamiltonian (state 54) i + (if i.val == 4861 then (-2771640702288 : Int) else 0)) = state 55 := funext step54_all
private theorem step55_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step55_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step55_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step55_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step55_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step55_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step55_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step55_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step55_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step55_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step55_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step55_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step55_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step55_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step55_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step55_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step55_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step55_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step55_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step55_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step55_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step55_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step55_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step55_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step55_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step55_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step55_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step55_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step55_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step55_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step55_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step55_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step55_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step55_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step55_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step55_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step55_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step55_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step55_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step55_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step55_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step55_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step55_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step55_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step55_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step55_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step55_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step55_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step55_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step55_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step55_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step55_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step55_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step55_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step55_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step55_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step55_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step55_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step55_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step55_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step55_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step55_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step55_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step55_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 55) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step55_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 55) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step55_part0 j
  · exact step55_part1 j
  · exact step55_part2 j
  · exact step55_part3 j
  · exact step55_part4 j
  · exact step55_part5 j
  · exact step55_part6 j
  · exact step55_part7 j
  · exact step55_part8 j
  · exact step55_part9 j
  · exact step55_part10 j
  · exact step55_part11 j
  · exact step55_part12 j
  · exact step55_part13 j
  · exact step55_part14 j
  · exact step55_part15 j
  · exact step55_part16 j
  · exact step55_part17 j
  · exact step55_part18 j
  · exact step55_part19 j
  · exact step55_part20 j
  · exact step55_part21 j
  · exact step55_part22 j
  · exact step55_part23 j
  · exact step55_part24 j
  · exact step55_part25 j
  · exact step55_part26 j
  · exact step55_part27 j
  · exact step55_part28 j
  · exact step55_part29 j
  · exact step55_part30 j
  · exact step55_part31 j
  · exact step55_part32 j
  · exact step55_part33 j
  · exact step55_part34 j
  · exact step55_part35 j
  · exact step55_part36 j
  · exact step55_part37 j
  · exact step55_part38 j
  · exact step55_part39 j
  · exact step55_part40 j
  · exact step55_part41 j
  · exact step55_part42 j
  · exact step55_part43 j
  · exact step55_part44 j
  · exact step55_part45 j
  · exact step55_part46 j
  · exact step55_part47 j
  · exact step55_part48 j
  · exact step55_part49 j
  · exact step55_part50 j
  · exact step55_part51 j
  · exact step55_part52 j
  · exact step55_part53 j
  · exact step55_part54 j
  · exact step55_part55 j
  · exact step55_part56 j
  · exact step55_part57 j
  · exact step55_part58 j
  · exact step55_part59 j
  · exact step55_part60 j
  · exact step55_part61 j
  · exact step55_part62 j
  · exact step55_part63 j
private theorem step55_all (i : Fin 8192) : (sparseHamiltonian (state 55) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 56 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step55_blocks b j
theorem step55 : (fun i => sparseHamiltonian (state 55) i + (if i.val == 4861 then (0 : Int) else 0)) = state 56 := funext step55_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
