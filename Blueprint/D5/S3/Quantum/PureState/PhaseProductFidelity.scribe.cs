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

    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Space(string field, params Formula[] dimensions) =>
        Seq(Field(field), Caret, Grp(Seq(dimensions)));
    private static Formula Nat(string name) => Seq(V(name), InMacro, Sp, Field("N"));
    private static Formula Index(string name, string size) =>
        Seq(D(1), Le, Sp, V(name), Le, Sp, V(size));
    private static Formula PhaseDomain() => Seq(Forall, Sp, Nat("n"), Comma,
        V("u"), InMacro, Sp, Space("C", V("n")), Comma, RowBreak);
    private static Formula Ensemble() => Seq(V("p"), InMacro, Sp, Space("R", V("m")),
        Comma, V("v"), InMacro, Sp, Space("C", V("m"), Times, Sp, V("n")));
    private static Formula SumIndex(string name, string size) =>
        Seq(Sum, Underscore, Grp(Index(name, size)), Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The best uniform purity-loss coefficient between the singleton and product phase encodings.",
        H("Purity of two phase encodings"),
        Blocks(
            Paragraph(Text("Encode a choice of n phases by the n + 1 amplitudes consisting of one "
                + "and the phases themselves. A second encoding uses all products indexed by subsets. "
                + "Its normalized vector is a tensor product of n equatorial qubit vectors. "
                + "Both squared overlaps depend only on the coordinatewise relative phases.")),
            Definition("simplex", "phase-simplex-overlap", "Singleton phase overlap",
                Seq(PhaseDomain(), Apply("A", V("u")), Eq,
                    Ratio(Sq(new Formula.Absolute(Seq(D(1), Plus, SumIndex("k", "n"),
                        Sub("u", "k")))), Sq(Par(V("n"), Plus, D(1))))),
                "For unit phases this is the squared inner product with the constant phase vector. "
                + "For a pair of inputs, take u to be their coordinatewise relative phase."),
            Definition("cube", "phase-product-overlap", "Product phase overlap",
                Seq(PhaseDomain(), Apply("B", V("u")), Eq, Prod, Underscore, Grp(Index("k", "n")),
                    Ratio(Seq(D(1), Plus, Re, Sp, Sub("u", "k")), D(2))),
                "Each unit complex coordinate contributes the squared overlap of the two "
                + "equatorial qubit states in that tensor factor."),
            Definition("mixedDeficit", "phase-ensemble-deficit", "Ensemble purity loss",
                Seq(Forall, Sp, Nat("m"), Comma, Nat("n"), Comma, V("F"), Colon, Sp,
                    Space("C", V("n")), To, Sp, Field("R"), Comma, Ensemble(), Comma, RowBreak,
                    Apply("L", V("F"), Comma, V("p"), Comma, V("v")), Eq,
                    SumIndex("i", "m"), SumIndex("j", "m"), Sub("p", "i"), Sub("p", "j"),
                    Par(D(1), Minus, Apply("F", Overline, Grp(Sub("v", "i")), Sub("v", "j")))),
                "The product of the conjugated row and the other row is coordinatewise. "
                + "Drawing two independent indices from the same distribution gives pairwise "
                + "weights p_i p_j. For a probability vector p, if F on each relative row equals the squared "
                + "inner product of the corresponding unit encoded states, this average loss is one minus "
                + "the purity of their mixture. The singleton and product overlaps meet this condition."),
            Describe.Lean(DescribeId.Create("phase-product-sharp-ensemble-coefficient"),
                DeclarationHandle.Create(Module + "mixed_coefficient_iff"),
                H("Sharp comparison for all finite phase ensembles"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Nat("n"), Comma, V("n"), Ge, D(1), Comma,
                    V("C"), InMacro, Sp, Field("R"), Comma, RowBreak,
                    Par(Forall, Sp, Nat("m"), Comma, Ensemble(), Comma, RowBreak,
                    Par(Par(Forall, Sp, Index("i", "m"), Comma, Sub("p", "i"), Ge, D(0)),
                        Land, Sp,
                        Par(Forall, Sp, Index("i", "m"), Comma, Index("k", "n"), Comma,
                            new Formula.Absolute(Sub("v", "ik")), Eq, D(1))), RowBreak,
                    Rightarrow, Sp, Apply("L", V("B"), Comma, V("p"), Comma, V("v")), Le, Sp, V("C"),
                    Apply("L", V("A"), Comma, V("p"), Comma, V("v"))),
                    Leftrightarrow, Factor(), Le, Sp, V("C")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here n is a positive integer, m is an arbitrary finite ensemble "
                    + "size, p is a nonnegative weight vector of length m, and v is an m by n array of "
                    + "unit complex phases. The bound permits every total weight. For a probability distribution it compares the two mixture purities. At n = 0 both losses vanish for every coefficient. With rows (1,1) and (-1,-1) and signed weights 2 and -1, the product loss is -4 and nine quarters times the singleton loss is -8. With a single entry 2 of weight one at n = 1, the product loss is -3/2 and the singleton loss is -21/4.")),
                    Paragraph(Text("The loss of a product of factors in the unit interval is at most "
                    + "the sum of their individual losses. The modulus of the sum of n phases is "
                    + "at most n. Expanding the singleton overlap then gives the displayed coefficient "
                    + "for each pair and multiplication by the nonnegative pair weights preserves it.")),
                    Paragraph(Text("For sharpness, give equal weights to the constant row and a row "
                    + "whose coordinates are all the same phase. As this phase approaches one, the "
                    + "ratio of the two losses tends to the claimed coefficient. When n equals two "
                    + "the coefficient is nine quarters."))), DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string name, string id, string title, Formula statement,
        string description) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);
}
