using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class QuadraticClassNumberSquareDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Comparing the actual Dedekind-zeta residue and the proved quadratic factorization identifies L(1). The squared functional equation gives L(0)^2=h^2 for the genuine maximal-order ideal class number. The finite doubling identity gives c^2=(2-chi(2))^2*h^2. Finite sign parity then proves h odd; positivity is the standard cardinality theorem. No class-number formula is an assumed premise.", H("QuadraticClassNumberSquare"), Blocks(
            Paragraph(Text("Comparing the actual Dedekind-zeta residue and the proved quadratic factorization identifies L(1). The squared functional equation gives L(0)^2=h^2 for the genuine maximal-order ideal class number. The finite doubling identity gives c^2=(2-chi(2))^2*h^2. Finite sign parity then proves h odd; positivity is the standard cardinality theorem. No class-number formula is an assumed premise.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-lfunction-one-eq-classnumber"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_one_eq_classNumber"), H("LFunction_one_eq_classNumber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The value at one is obtained from the genuine number-field residue and the quadratic Euler factorization. No finite character-sum formula is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-lfunction-zero-sq-classnumber"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_zero_sq_classNumber"), H("LFunction_zero_sq_classNumber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The squared functional equation suffices: its sign need not be computed to identify the square of L(0) with the square of the actual ideal class number."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-quadraticexcess"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess"), H("quadraticExcess"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An integer-valued half-interval character sum, including its zero term. The value is independent of the class-number definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-quadraticexcess-sq-classnumber"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_sq_classNumber"), H("quadraticExcess_sq_classNumber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Sufficient actual-class-number bridge for congruences depending on h squared. In particular, this does not redefine h as a character sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-quadraticexcess-eq-range"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_eq_range"), H("quadraticExcess_eq_range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Least representatives identify the excess with its literal finite positive interval; the additional index zero contributes zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-quadraticexcess-mod-two"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_mod_two"), H("quadraticExcess_mod_two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every nonzero lower-half character value is odd, so the excess has the parity of the interval length. In this prime family that length is odd."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticclassnumbersquare-classnumber-odd"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.classNumber_odd"), H("classNumber_odd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Oddness of the genuine maximal-order class number follows from the proved squared bridge and the parity of the finite interval."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Zeta/QuadraticZetaFactorization")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants"))]));
}
