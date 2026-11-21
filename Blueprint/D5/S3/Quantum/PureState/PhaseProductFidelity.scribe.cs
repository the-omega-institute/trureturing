using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseProductFidelityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseProductFidelity.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Sub(string name, string index) =>
        Seq(V(name), Underscore, Grp(V(index)));
    private static Formula Par(params Formula[] items) => Seq(Open, Seq(items), Close);
    private static Formula Sq(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Ratio(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Apply(string name, params Formula[] args) => Seq(V(name), Par(args));
    private static Formula Factor() => Ratio(Sq(Par(V("n"), Plus, D(1))), D(4));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The best uniform purity-loss coefficient between the singleton and product phase encodings.",
        H("Purity of two phase encodings"),
        Blocks(
            Paragraph(Text("Encode a choice of n phases by the n + 1 amplitudes consisting of one "
                + "and the phases themselves. A second encoding uses all products indexed by subsets. "
                + "Its normalized vector is a tensor product of n equatorial qubit vectors. "
                + "Both squared overlaps depend only on the coordinatewise relative phases.")),
            Definition("simplex", "phase-simplex-overlap", "Singleton phase overlap",
                Seq(Apply("A", V("u")), Eq,
                    Ratio(Sq(new Formula.Absolute(Seq(D(1), Plus, Sum, Underscore, Grp(V("k")),
                        Sub("u", "k")))), Sq(Par(V("n"), Plus, D(1))))),
                "For unit phases this is the squared inner product with the constant phase vector. "
                + "For a pair of inputs, take u to be their coordinatewise relative phase."),
            Definition("cube", "phase-product-overlap", "Product phase overlap",
                Seq(Apply("B", V("u")), Eq, Prod, Underscore, Grp(V("k")),
                    Ratio(Seq(D(1), Plus, Re, Sp, Sub("u", "k")), D(2))),
                "Each unit complex coordinate contributes the squared overlap of the two "
                + "equatorial qubit states in that tensor factor."),
            Definition("mixedDeficit", "phase-ensemble-deficit", "Ensemble purity loss",
                Seq(Apply("L", V("F"), Comma, V("p"), Comma, V("v")), Eq, Sum,
                    Underscore, Grp(V("i"), Comma, V("j")), Sub("p", "i"), Sub("p", "j"),
                    Par(D(1), Minus, Apply("F", Overline, Grp(Sub("v", "i")), Sub("v", "j")))),
                "The product of the conjugated row and the other row is coordinatewise. "
                + "Drawing two independent indices from the same distribution gives pairwise "
                + "weights p_i p_j. For normalized states this average loss is one minus the "
                + "purity of their mixture."),
            Describe.Lean(DescribeId.Create("phase-product-sharp-ensemble-coefficient"),
                DeclarationHandle.Create(Module + "mixed_coefficient_iff"),
                H("Sharp comparison for all finite phase ensembles"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, V("n"), Ge, D(1), Comma, V("C"), InMacro, Mathbb, Grp(V("R")),
                    Comma, RowBreak, Par(Forall, Sp, V("m"), Comma, V("p"), Comma, V("v"),
                    Comma, Par(Sub("p", "i"), Ge, D(0), Comma, Sum, Underscore, Grp(V("i")),
                    Sub("p", "i"), Eq, D(1), Comma, new Formula.Absolute(Sub("v", "ik")), Eq, D(1)),
                    Rightarrow, Sp, Apply("L", V("B"), Comma, V("p"), Comma, V("v")), Le, Sp, V("C"),
                    Apply("L", V("A"), Comma, V("p"), Comma, V("v"))),
                    Leftrightarrow, Factor(), Le, Sp, V("C")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here n is a positive integer, m is an arbitrary finite ensemble "
                    + "size, p is a probability vector of length m, and v is an m by n array of "
                    + "unit complex phases. All coordinate conditions range over their full index sets.")),
                    Paragraph(Text("The loss of a product of factors in the unit interval is at most "
                    + "the sum of their individual losses. The modulus of the sum of n phases is "
                    + "at most n. Expanding the singleton overlap then gives the displayed coefficient "
                    + "for each pair and multiplication by the nonnegative pair weights preserves it.")),
                    Paragraph(Text("For sharpness, give equal weights to the constant row and a row "
                    + "whose coordinates are all the same phase. As this phase approaches one, the "
                    + "ratio of the two losses tends to the claimed coefficient. For two independent "
                    + "phases the coefficient is nine quarters."))), DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string name, string id, string title, Formula statement,
        string description) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);
}
