using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class TriangleFourSymbolNecessityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/TriangleFourSymbolNecessity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original finite stochastic triangle laws at the entropy-cost equality have a binary block form when their positive output support has size two to four.",
        H("Four-Symbol Necessity on the Original Triangle Law"),
        Blocks(
            Paragraph(Text(
                "The carrier has arbitrary finite original source and output alphabets. "
                + "Its source law nu is nonnegative and normalized. The incident kernels "
                + "KA(s2,s3), KB(s3,s1), KC(s1,s2) are nonnegative and each row sums to one. "
                + "The six-variable response law is nu times the three response probabilities. "
                + "Agreement means that every off-diagonal response cell has zero mass. "
                + "The record law is the actual marginal of the first output and all three sources. "
                + "The source cost is KL(nu || mu1 times mu2 times mu3), where each mui is "
                + "the marginal of that same source law. Entropy uses natural logarithms.")),
            Node("original_law_recoverability", "Agreement forces the active original rows",
                "Assume agreement. At each positive source cell, the product response law and agreement force "
                + "all three response vectors to be point masses at one common symbol. "
                + "Every positive incident-pair marginal has a positive extension. Thus its "
                + "fixed kernel row is a point mass. The incident readouts agree on every "
                + "positive source cell, and the record-cell identity also covers zero source cells."),
            Node("original_law_common_record", "The common record belongs to the same law",
                "Assume agreement. Summing the six-variable law over the other two outputs gives recordLaw. "
                + "The output weights are a probability vector. Replacing the first response "
                + "by either other incident response gives the same record/source joint law."),
            Node("original_equality_fibers", "The KL equality forces source-pair and fiber products",
                "Assume agreement and sourceCost = H(outputLaw)/2. Then all three unconditional source pairs "
                + "are products of the original marginals. For each positive original output "
                + "symbol, the entire conditional source law is a threefold product, including "
                + "its zero cells. The proof uses the exact balance of twice the source cost "
                + "minus output entropy into three pair mutual informations and the weighted "
                + "conditional dual total correlations. Every term is nonnegative. The entropy "
                + "chain rule, zero mutual-information product characterization and strong "
                + "subadditivity equality theorem apply to these explicitly linked finite laws."),
            Node("original_output_cardinality", "A nonconstant equality record has at least four symbols",
                "Assume agreement, sourceCost = H(outputLaw)/2 and at least two positive outputs. "
                + "For a positive source symbol, take the support of its conditional distribution "
                + "over positive output symbols. Each of the three support families covers every "
                + "positive output. A support row from either of two different families meets "
                + "the other row in exactly one symbol. No coordinate can occur in every row of "
                + "two families: coverage of a second coordinate would contradict their unique "
                + "intersection. Consequently each row and its complement contain at least two "
                + "symbols. This proves the four-symbol lower bound without a full-support assumption."),
            Node("original_binary_supports", "Original posterior supports determine binary parity labels",
                "Assume agreement, sourceCost = H(outputLaw)/2 and two to four positive outputs. "
                + "Then every support row and its complement "
                + "have size two. Two distinct rows from one family are disjoint: if they shared "
                + "one symbol, rows in each other family containing that symbol would also have "
                + "to contain the single remaining coordinate, contradicting unique intersection. "
                + "Each family therefore consists of two complementary support sets, both occurring "
                + "on actual positive source symbols. Two family labels give a bijection h from "
                + "Bool times Bool onto the positive original output support. The third label is "
                + "their exclusive-or after relabelling its two blocks. Distinct original symbols "
                + "with the same posterior remain distinct source symbols."),
            Node("original_law_necessity", "Complete necessity for the original source and response laws",
                "Assume agreement, the original KL equality and two to four positive output "
                + "symbols. Then there are exactly four positive outputs and an output bijection "
                + "h. On every original source alphabet there are two nonnegative normalized "
                + "probability vectors qi(0), qi(1) with disjoint supports. Their full original "
                + "record/source law is the displayed cell formula. The source-block masses are "
                + "forced to one half and every positive output mass to one quarter: the three "
                + "pair-product identities, combined with parity, force these values. The "
                + "conditional source distribution on each block is twice its original marginal "
                + "there, and zero elsewhere. Arbitrary unequal masses inside a block and any "
                + "further zero coordinates are preserved."),
            Paragraph(Math(Disp(CellFormula()))),
            Paragraph(Text(
                "Here u and v are Boolean labels, addition in the third exponent is modulo two, "
                + "and the formula holds for every original source triple. For each original "
                + "source symbol s, qi(0)(s) times qi(1)(s) is zero. Each qi(b) sums to one on the "
                + "whole original alphabet. The bijection lands in the positive output subtype, "
                + "so unused symbols of the original output alphabet remain outside its image.")),
            Paragraph(Text(
                "On a positive incident pair with block labels v,w, KA is the point mass at "
                + "h(v xor w,v). On labels w,u, KB is the point mass at h(u,u xor w). On labels "
                + "u,v, KC is the point mass at h(u,v). These are equalities of every coordinate "
                + "of the actual original kernel rows. Inactive normalized rows are unrestricted.")),
            Paragraph(Text(
                "The converse construction and the separate entropy formulas are not part of "
                + "this necessity theorem. No classification for more than four positive outputs "
                + "or claim of publication priority is made.")))));

    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("triangle-original-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Q(byte i, Formula bit) => Seq(F.Id("q"), Underscore, Grp(D(i)),
        Caret, Grp(bit), Open, F.Id("s"), Underscore, Grp(D(i)), Close);

    private static Formula CellFormula() => Seq(F.Id("P"), Open, F.Id("X"), Eq,
        Call("h", F.Id("u"), F.Id("v")), Comma, Sp, F.Id("S"), Eq, F.Id("s"), Close,
        Eq, new Formula.Fraction(D(1), D(4)), Sp, Q(1, F.Id("u")), Sp,
        Q(2, F.Id("v")), Sp, Q(3, Seq(F.Id("u"), Plus, F.Id("v"))));
}
