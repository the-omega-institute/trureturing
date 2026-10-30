using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class MutuallyUnbiasedDiagonalPlanesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mutual unbiasedness is exactly orthogonality of the traceless diagonal planes.",
        H("Mutually Unbiased Diagonal Planes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mutually-unbiased-coordinate-projector-two"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.coordinateProjectorTwo"),
                H("The two coordinate projectors"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Parenthesized(Seq(Named("coordinateProjectorTwo"), Colon, Sp,
                        new Formula.TypeArrow(new Formula.Apply(Named("Fin"), [D(2)]),
                            new Formula.Apply(Named("Matrix"),
                                [new Formula.Apply(Named("Fin"), [D(2)]),
                                 new Formula.Apply(Named("Fin"), [D(2)]),
                                 Seq(Mathbb, Grp(F.Id("C")))])))),
                    FormulaRelationOperator.Equal,
                    Seq(Bang, OpenBracket,
                        Seq(Bang, Bang, OpenBracket, D(1), Comma, D(0), Semi,
                            D(0), Comma, D(0), CloseBracket), Comma,
                        Seq(Bang, Bang, OpenBracket, D(0), Comma, D(0), Semi,
                            D(0), Comma, D(1), CloseBracket), CloseBracket)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two complex qubit coordinate projectors select the first and second basis vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mutually-unbiased-coordinate-context-two"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.coordinateContextTwo"),
                H("The coordinate rank-one context"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    new Formula.Apply(
                        Seq(Operatorname, Grp(F.Id("RankOneContext")), Dot,
                            Operatorname, Grp(F.Id("projector"))),
                        [Parenthesized(Seq(Named("coordinateContextTwo"), Colon, Sp,
                            new Formula.Apply(Named("RankOneContext"), [D(2)])))]),
                    FormulaRelationOperator.Equal,
                    Seq(Operatorname, Grp(F.Id("coordinateProjectorTwo")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The context has coordinateProjectorTwo as its projector family. Each member is Hermitian, idempotent and trace one, and compresses every matrix X to trace(PX) times P. The two members sum to the identity. These properties supply the rankOne and resolvesIdentity fields of RankOneContext; its projector family determines the context because the other fields are proofs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mutually-unbiased-diagonal-planes"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes."
                        + "mutually_unbiased_diagonal_planes"),
                H("Mutually unbiased diagonal planes"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B and C be complete rank-one projective basis contexts in complex "
                            + "dimension d, with d at least two. Mutual unbiasedness means that "
                            + "every cross-context projector overlap has real trace equal to the "
                            + "inverse of d.")),
                    Paragraph(Text(
                        "The diagonal plane of a context is constructed on the exact real "
                            + "trace-zero Hermitian carrier: subtract the scalar trace component "
                            + "from each rank-one projector and take their real span. The two "
                            + "planes are orthogonal exactly when all cross overlaps are uniform.")),
                    Paragraph(Text(
                        "Equivalently, both orders of the unread projective measurement vanish "
                            + "on every trace-zero Hermitian matrix. On an arbitrary Hermitian "
                            + "matrix, both orders instead return its scalar trace component, "
                            + "namely the trace divided by d times the identity.")),
                    Paragraph(Text(
                        "All four equivalences are public. The proof expands the centered "
                            + "Hilbert--Schmidt pairing, applies the rank-one compression law, and "
                            + "uses the identity resolution to evaluate both measurement "
                            + "compositions. Repository, pinned-library, and Loogle searches found "
                            + "no theorem packaging these clauses on the same carriers."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula basisB = F.Id("B");
        Formula basisC = F.Id("C");
        Formula unbiased = Apply("MutuallyUnbiased", basisB, basisC);
        Formula orthogonalPlanes = Apply("OrthogonalTracelessPlanes", basisB, basisC);
        Formula zeroComposition = Apply("TraceZeroComposition", basisB, basisC);
        Formula scalarComposition = Apply("ScalarTraceComposition", basisB, basisC);

        return Disp(Seq(
            Open, unbiased, Sp, Iff, Sp, orthogonalPlanes, Close, Sp, Land, Sp, RowBreak,
            Open, orthogonalPlanes, Sp, Iff, Sp, zeroComposition, Close, Sp, Land, Sp, RowBreak,
            Open, zeroComposition, Sp, Iff, Sp, scalarComposition, Close, Sp, Land, Sp, RowBreak,
            Open, scalarComposition, Sp, Iff, Sp, unbiased, Close, Dot));
    }
}
