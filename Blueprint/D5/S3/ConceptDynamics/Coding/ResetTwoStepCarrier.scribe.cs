using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetTwoStepCarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetTwoStepCarrier.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Coefficient(string matrix) => Call("coefficientAt",
        Call(matrix, I("q")), Call("origin", I("hq")), Call("origin", I("hq")), I("SignIdentity"));
    private static DocumentBlock Record(string name, string id, string title,
        string matrix, int value, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
                [B("q", I("Nat")), B("hq", Call("NatPositive", I("q")))],
                Equal(Coefficient(matrix), Num(value))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual reset square and its identity summand retain their separate origin coefficients for every positive order.",
        H("Two-step reset carrier coefficients"),
        Blocks(
            Paragraph(Text("Sign is Multiplicative Bool with the original XOR law, and SignIdentity "
                + "is its identity. resetMatrix q has the reset label ofAdd true into age zero and "
                + "the identity-labelled advance when the next age is less than q. twoStepMatrix q "
                + "is the product resetMatrix q * resetMatrix q, and twoStepCarrier q adds the "
                + "identity matrix. origin hq is age zero; NatPositive(q) means 0<q. "
                + "coefficientAt(M,i,j,g) denotes the natural-number coefficient of g in M(i,j).")),
            Record("twoStep_origin_square_coeff", "two-step-origin-square-coefficient",
                "The reset square has one identity-labelled origin path",
                "twoStepMatrix", 1,
                "In the product coefficient sum, the intermediate age zero contributes the "
                    + "two reset edges FF. Their two flip labels multiply to the identity. "
                    + "Every other intermediate age contributes zero to this coefficient. "
                    + "The conclusion holds for all positive q, including q=1 where advances are absent."),
            Record("twoStep_origin_coeff", "two-step-origin-carrier-coefficient",
                "The carrier has two separately numbered origin boundaries",
                "twoStepCarrier", 2,
                "The identity summand contributes one coefficient and the reset square contributes "
                    + "one. Thus the empty path and FF occupy distinct coefficient numbers zero "
                    + "and one, even though both have the same origin endpoints and identity label. "
                    + "ResetTwoStepArithmetic uses this coefficient calculation in its actual "
                    + "numberedBoundaryEquiv for every positive q. The history automorphism in "
                    + "that module separately retains the hypothesis 4 divides q; the coefficient "
                    + "calculation imposes no such restriction."))));
}
