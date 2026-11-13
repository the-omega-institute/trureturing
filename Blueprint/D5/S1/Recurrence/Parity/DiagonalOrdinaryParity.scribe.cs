using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DiagonalOrdinaryParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.";
    private static readonly LibraryNoteRef ParitySource =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a177775");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized diagonal-constraint series has odd ordinary coefficients exactly at powers of two.",
        H("Ordinary Coefficient Parity of the Diagonal-Constraint Series"),
        Blocks(
            Paragraph(Text("OEIS A177775 is the ordinary coefficient sequence of the same "
                + "generatingSeries G. The initial values are G(0)=0 and coeff(1,G)=coeff(2,G)=1; "
                + "they are specified by the original recursive program and by the revised "
                + "seed [0,1,1]. The NAME's adjacent-iterate condition holds for every n>2. "
                + "The construction and uniqueness in DiagonalIterateEven identify this normalized source "
                + "without assuming existence or integrality. Its ordinary coefficients "
                + "are coeff(n,G); DiagonalIterateEven.a(n) denotes the different diagonal sequence A395842. "
                + "The second OEIS offset component 3 adds no initial condition. "
                + "The A177775 conclusion includes every n≥1, both implications, and n=1=2^0. "
                + "The PARI programs themselves are not formalized.")),
            Node("result", "The full A177775 ordinary-coefficient parity characterization",
                Disp(Seq(Bound("n", Naturals()), Implication(Seq(D(1), Sp, Le, Sp, N()),
                    Parens(Seq(Call("Odd", Coeff(N(), G())), Sp, Iff, Sp,
                        Parens(Seq(Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
                            Equal(N(), new Formula.Power(D(2), F.Id("k")))))))))),
                "Let P be CubicFifteenSubstitutionParity.powerTwoSeries over ZMod(2). "
                + "Its coefficient at n is the indicator of existence of a natural k with n=2^k. "
                + "The first component of thue_series_equation and characteristic two give "
                + "P+P²=X. The existing H satisfies H+H²=X, and both constant coefficients "
                + "are zero. CubicFifteenSubstitutionParity.quadratic_unique therefore gives "
                + "H=P. The existing mod_two_identity identifies the coefficientwise reduction "
                + "of G with H. Applying coeff(n) and ZMod.intCast_eq_one_iff_odd proves "
                + "the displayed equivalence in both directions for every positive n. "
                + "The zeroth exponent k=0 supplies n=1. This uses ordinary integer coefficients "
                + "of G and imposes no parity assumption on its construction.",
                provenance: AssessedProvenance.FromRepo(ParitySource)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("diagonal-ordinary-parity-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(ParitySource), Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N() => F.Id("n");
    private static Formula G() => Call("DiagonalIterateEven.generatingSeries");
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
    private static Formula Implication(Formula premise, Formula result) =>
        Seq(Parens(premise), Sp, Implies, Sp, result);
}
