using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TriangularPathNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Fn(string s, params Formula[] args) => Call(s, args);
    private static ScribeNode Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary output laws of reduced triangular paths.",
        H("Reduced Triangular Paths"), Blocks(
            Def("State", "Residual and retained labels", Fn("State", V("r"), V("e")),
                "A state consists of natural numbers r and e. The first counts residual cylinders; "
                + "the second counts labels sharing the anchor prefix. Legal states satisfy 0 <= r < e <= m."),
            Def("Action", "Two column actions", Seq(V("one"), Sp, Lor, Sp, Fn("zero", V("h"))),
                "The one action writes one to every retained label. The zero action writes one "
                + "only to the last h retained labels, which then leave the retained group."),
            Def("successor", "Successor state", Fn("successor", V("s"), V("a")),
                "For one the successor is (2r-e,e). For zero(h) it is (2r-h,e-h). "
                + "Natural subtraction is exact under the corresponding legal action conditions."),
            Def("Legal", "Legal state and action", Fn("Legal", V("m"), V("s"), V("a")),
                "In addition to 0 < e, r < e and e <= m, one requires e <= 2r. "
                + "The zero(h) action instead requires 2r < e and h <= 2r. "
                + "At (0,e), only zero(0) is legal and the successor equals the original state."),
            Def("RootPath", "Legal infinite root path", Fn("RootPath", V("m")),
                "A path gives a state and action at every natural depth, starts at (1,m), "
                + "and satisfies legality and the successor equation at every step. "
                + "A terminating path is extended by its zero residual self-loop."),
            Def("anchorDigit", "Anchor digit", Fn("anchorDigit", V("a")),
                "The anchor digit is one for the one action and zero for every zero(h) action."),
            Def("digit", "Actual label digit", Fn("digit", V("gamma"), V("i"), V("d")),
                "Indices i in Fin(m) represent labels i+1. At depth d, labels outside 0 <= i < e "
                + "write zero. Retained labels write one for the one action; under zero(h), "
                + "precisely e-h <= i < e write one. The digit belongs to Fin(2)."),
            Def("probability", "Output probability", Equal(Fn("p", V("i")),
                Fn("tsum", Seq(Fn("a", V("i"), V("d")), Sp, V("/"), Sp,
                    new Formula.Power(D(2), Seq(V("d"), Plus, D(1)))))),
                "For each label, its probability is the sum of its depth d digit divided by "
                + "2^(d+1), for d starting at zero. Digits are interpreted as real numbers."),
            Def("anchorMass", "Anchor probability", Equal(V("t"),
                Fn("tsum", Seq(Fn("b", V("d")), Sp, V("/"), Sp,
                    new Formula.Power(D(2), Seq(V("d"), Plus, D(1)))))),
                "The anchor mass is the same binary series formed from the anchor digits."),
            Def("pathCost", "Residual layer cost", Equal(V("C"),
                Fn("tsum", Seq(Fn("r", V("d")), Sp, V("/"), Sp, new Formula.Power(D(2), V("d"))))),
                "The path cost sums r_d/2^d over all depths. It counts expected paid bits, "
                + "rather than charging r_d bits for a single transition."),
            Def("binaryPrefix", "Integer digit prefix", Equal(Fn("prefix", V("i"), Seq(V("d"), Plus, D(1))),
                Seq(D(2), Cdot, Fn("prefix", V("i"), V("d")), Plus, Fn("a", V("i"), V("d")))),
                "The empty prefix is zero. Each new digit doubles the previous prefix and "
                + "adds that digit. Thus a length D prefix represents the weighted sum "
                + "of digits with weights 2^(D-1-d)."))));
}
