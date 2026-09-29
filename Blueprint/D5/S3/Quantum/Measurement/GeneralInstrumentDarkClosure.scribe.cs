using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class GeneralInstrumentDarkClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure.";

    private static readonly Formula D = F.Id("d"), N = F.Id("n"), V = F.Id("V"), Vec = F.Id("v");
    private static readonly Formula AlphaSet = Alpha, IotaSet = Iota;
    private static readonly Formula A = F.Id("a"), I = F.Id("i"), X = F.Id("X");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a general no-click instrument on a d-dimensional space, the dark layers are the kernels of the "
            + "survival defects, they stop changing after d steps, and the last layer is the largest subspace "
            + "that every click operator annihilates and every no-click operator maps into itself.",
        H("Finite Closure of Dark Directions for General Instruments"),
        Blocks(
            Node("dual", "The dual no-click map",
                Disp(Seq(Cal(X), Sp, Eq, Sp, Sum, Underscore, Grp(A, Sp, InMacro, Sp, AlphaSet), Sp,
                    QAdj(A), Sp, X, Sp, Sub("Q", A))),
                "The no-click operation acts by the Kraus operators Q_a, labelled by the finite unread set alpha; "
                    + "its dual on effects is the map above.",
                "noClickDual", DescribeRole.Definition),
            Node("survival", "Survival effects",
                Disp(Seq(Sub("S", D0()), Sp, Eq, Sp, F.Id("I"), Comma, Qquad, Sp,
                    Sub("S", Seq(N, Plus, D1())), Sp, Eq, Sp, Cal(Sub("S", N)))),
                "The n-step survival effect is the n-fold dual no-click map applied to the identity.",
                "survival", DescribeRole.Definition),
            Node("layer", "Dark layers",
                Disp(Seq(Sub("D", D0()), Sp, Eq, Sp, Space(), Comma, Qquad, Sp,
                    Sub("D", Seq(N, Plus, D1())), Sp, Eq, Sp, OpenBrace, Vec, Sp, InMacro, Sp, Space(), Sp, Mid, Sp,
                    Sub("L", I), Sp, Vec, Sp, Eq, Sp, D0(), Sp, F.Text, Grp(Sp, F.Id("for"), Sp, F.Id("all"), Sp), I, Comma, Sp,
                    Sub("Q", A), Sp, Vec, Sp, InMacro, Sp, Sub("D", N), Sp, F.Text, Grp(Sp, F.Id("for"), Sp, F.Id("all"), Sp), A, CloseBrace)),
                "A vector lies in the next layer when no click operator L_i sees it and every unread no-click branch "
                    + "sends it into the current layer.",
                "darkLayer", DescribeRole.Definition),
            Node("closure", "Finite closure of the dark layers", TheoremFormula(),
                "Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the "
                    + "d-dimensional space, and assume the completeness relation. The defect I - S_{n+1} equals the "
                    + "sum of L_i^* L_i and of Q_a^* (I - S_n) Q_a, so every defect is positive semidefinite, and the "
                    + "kernel of a sum of positive semidefinite operators is the intersection of their kernels. By "
                    + "induction the kernel of I - S_n is the n-th dark layer. The layers decrease; one equality "
                    + "between consecutive layers persists forever, and every strict step lowers the dimension, so "
                    + "the layers are constant from n = d on. The stable layer is annihilated by every L_i and mapped "
                    + "into itself by every Q_a, and by induction every subspace with these two properties lies in "
                    + "every layer.",
                "darkLayer_closure", DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complete = Seq(
            Sum, Underscore, Grp(A, Sp, InMacro, Sp, AlphaSet), Sp, QAdj(A), Sp, Sub("Q", A), Sp, Plus, Sp,
            Sum, Underscore, Grp(I, Sp, InMacro, Sp, IotaSet), Sp,
            Sub("L", I), Caret, Grp(Star), Sp, Sub("L", I), Sp, Eq, Sp, F.Id("I"));
        Formula kernels = Seq(
            Forall, Sp, N, Comma, Sp, Sub("D", N), Sp, Eq, Sp,
            Operatorname, Grp(F.Id("ker")), Open, F.Id("I"), Minus, Sub("S", N), Close);
        Formula stable = Seq(
            Forall, Sp, N, Sp, Geq, Sp, D, Comma, Sp, Sub("D", N), Sp, Eq, Sp, Sub("D", D));
        Formula invariant = Seq(
            Sub("L", I), Sp, Sub("D", D), Sp, Eq, Sp, D0(), Comma, Sp,
            Sub("Q", A), Sp, Sub("D", D), Sp, Subseteq, Sp, Sub("D", D), Sp, F.Text, Grp(Sp, F.Id("for"), Sp, F.Id("all"), Sp), I, Comma, Sp, A);
        Formula maximal = Seq(
            Forall, Sp, V, Sp, Subseteq, Sp, Space(), Comma, Sp,
            Open, Sub("L", I), Sp, V, Sp, Eq, Sp, D0(), Sp, Land, Sp, Sub("Q", A), Sp, V, Sp, Subseteq, Sp, V,
            Sp, F.Text, Grp(Sp, F.Id("for"), Sp, F.Id("all"), Sp), I, Comma, Sp, A, Close, Sp, Rightarrow, Sp, V, Sp, Subseteq, Sp, Sub("D", D));
        return Disp(Seq(
            complete, Sp, Rightarrow, RowBreak, Grp(),
            kernels, Comma, Quad, Sp, stable, Comma, RowBreak, Grp(),
            invariant, Comma, RowBreak, Grp(),
            maximal, Dot));
    }

    private static Formula D0() => F.D(0);

    private static Formula D1() => F.D(1);

    private static Formula Space() => Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(D));

    private static Formula Cal(Formula argument) => Seq(Mathcal, Grp(F.Id("A")), Open, argument, Close);

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));

    private static Formula QAdj(Formula index) => Seq(F.Id("Q"), Underscore, Grp(index), Caret, Grp(Star));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("general-dark-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
