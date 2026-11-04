using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.QuadraticFields;

internal sealed class QuadraticImaginaryInvariantsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The negative discriminant excludes real embeddings. The field has one complex place and unit rank zero. The regulator is its zero-dimensional determinant and the two actual torsion units give the residue pi times the genuine ideal class number divided by sqrt(p).", H("QuadraticImaginaryInvariants"), Blocks(
            Paragraph(Text("The negative discriminant excludes real embeddings. The field has one complex place and unit rank zero. The regulator is its zero-dimensional determinant and the two actual torsion units give the residue pi times the genuine ideal class number divided by sqrt(p).")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticimaginaryinvariants-complexplaces"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.complexPlaces"), H("complexPlaces"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary.complexPlaces supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticimaginaryinvariants-unitrank"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.unitRank"), H("unitRank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary.unitRank supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticimaginaryinvariants-field-regulator"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_regulator"), H("field_regulator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A real embedding would give a real square equal to the negative integer minus p. -/ instance totallyComplex : NumberField.IsTotallyComplex (Field p) where isComplex w := by rw [← not_isReal_iff_isComplex] intro hw let φ := embedding_of_isReal hw let ω : Field p := QuadraticAlgebra.omega have hω : ω * ω = (orderA p : Field p) + ω := by simpa [ω, Algebra.smul_def] using (QuadraticAlgebra.omega_mul_omega_eq_add (a := (orderA p : ℚ)) (b := (1 : ℚ))) have heq := congrArg φ hω simp only [map_mul, map_add, map_intCast] at heq have hD : (1 : ℝ) + 4 * (orderA p : ℝ) = -(p : ℝ) := by exact_mod_cast (show 1 + 4 * orderA p = -(p : ℤ) by simpa only [QuadraticAlgebra.discr_def, one_pow] using order_discr p) have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos nlinarith [sq_nonneg (2 * φ ω - 1)] theorem complexPlaces : nrComplexPlaces (Field p) = 1 := by have h := NumberField.IsTotallyComplex.finrank (Field p) rw [QuadraticAlgebra.finrank_eq_two] at h omega theorem unitRank : NumberField.Units.rank (Field p) = 0 := by rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, complexPlaces] /-- The regulator is the determinant in dimension zero, with the Mathlib normalization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticimaginaryinvariants-field-torsionorder"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_torsionOrder"), H("field_torsionOrder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual maximal order has exactly two torsion units once p greater than three."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticimaginaryinvariants-zeta-residue"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.zeta_residue"), H("zeta_residue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Specialization of the genuine number-field residue expression, retaining the actual cardinality of the maximal-order ideal class group. This is field data, not yet the quadratic Dedekind-zeta/Dirichlet-L identification."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal"))]));
}
