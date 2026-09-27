using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class GeneralInstrumentEffectClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure.";

    private static readonly Formula N = F.Id("N"), NStar = Seq(F.Id("N"), Underscore, Grp(Star)), A = F.Id("a"), I = F.Id("i");
    private static readonly Formula X = F.Id("x"), Dim = F.Id("d"), Lab = F.Id("lab");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a general no-click instrument on a d-dimensional space, the real spaces spanned by the identity and "
            + "the first-event effects stop growing within d^2 rounds, and the stable space is invariant under the "
            + "dual no-click map.",
        H("Finite Closure of First-Event Effect Spaces"),
        Blocks(
            Node("click-effect", "Click effects",
                Disp(Seq(Sub("B", X), Sp, Eq, Sp, Sum, Underscore, Grp(Operatorname, Grp(Lab), Open, I, Close, Sp,
                    Eq, Sp, X), Sp, Sub("L", I), Caret, Grp(Star), Sp, Sub("L", I))),
                "The click Kraus operator L_i records the readable outcome lab(i); the effect of outcome x collects "
                    + "all click operators with that label.",
                "clickEffect", DescribeRole.Definition),
            Node("effect-space", "Effect spaces",
                Disp(Seq(Sub("V", N), Sp, Eq, Sp, Operatorname, Grp(F.Id("span")), Underscore, Grp(Mathbb,
                    Grp(F.Id("R"))), Open, OpenBrace, F.Id("I"), CloseBrace, Sp, Cup, Sp, OpenBrace,
                    Mathcal, Grp(F.Id("A")), Caret, Grp(F.Id("n")), Open, Sub("B", X), Close, Sp, Mid, Sp,
                    F.Id("n"), Sp, Lt, Sp, N, Comma, Sp, X, Sp, InMacro, Sp, Xi, CloseBrace, Close)),
                "The real linear span, inside the complex d by d matrices, of the identity and the effects of all "
                    + "first clicks within the first N rounds.",
                "effectSpace", DescribeRole.Definition),
            Node("closure", "Finite closure of the effect spaces", TheoremFormula(),
                "Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators with the "
                    + "completeness relation and d >= 1. Since A(I) = I minus the sum of the click effects and "
                    + "A applied to A^n(B_x) is A^{n+1}(B_x), the spaces satisfy V_{N+1} = V_1 + A(V_N); so one "
                    + "equality V_{k+1} = V_k persists for all later N, and it also shows A(V_k) inside V_k. Every "
                    + "generator is Hermitian, and the Hermitian d by d matrices form a real space of dimension "
                    + "d^2, so every V_N has real dimension at most d^2. As V_1 contains the identity and each strict step raises the "
                    + "dimension, some k between 1 and d^2 satisfies V_{k+1} = V_k.",
                "effectSpace_closure", DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complete = Seq(
            Sum, Underscore, Grp(A, Sp, InMacro, Sp, Alpha), Sp, Sub("Q", A), Caret, Grp(Star), Sp, Sub("Q", A),
            Sp, Plus, Sp, Sum, Underscore, Grp(I, Sp, InMacro, Sp, Iota), Sp,
            Sub("L", I), Caret, Grp(Star), Sp, Sub("L", I), Sp, Eq, Sp, F.Id("I"));
        return Disp(Seq(
            Dim, Sp, Geq, Sp, D(1), Sp, Land, Sp, complete, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, NStar, Comma, Sp, D(1), Sp, Leq, Sp, NStar, Sp, Leq, Sp, Dim, Caret, Grp(D(2)), Comma, Quad,
            Sp, Forall, Sp, N, Sp, Geq, Sp, NStar, Comma, Sp, Sub("V", N), Sp, Eq, Sp, Sub("V", NStar), Comma, Quad,
            Sp, Mathcal, Grp(F.Id("A")), Open, Sub("V", NStar), Close, Sp, Subseteq, Sp, Sub("V", NStar), Dot));
    }

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("effect-closure-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
