using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class PairedZeroSubsetSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient-one zero subsets of signed C3 coordinate bases",
        H("Coefficient-one zero subsets of signed C3 coordinate bases"),
        Blocks(
            Paragraph(Text(
                    "V(r) is the original coordinate group Fin r to ZMod 3. The existential includes "
                    + "uniqueness: every other pair-index set J giving the same original subset equals I.")),
            Paragraph(Text(
                    "For a natural rank r, work in the original additive group Fin r to ZMod 3. Write e_i for "
                    + "Pi.single i 1. The alphabet is the image of (i,b) mapped to e_i or minus e_i. Injectivity "
                    + "distinguishes coordinates and signs, so there are exactly 2r distinct nonzero labels.")),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum.zero_subset_spectrum"),
                H("Zero subsets are exactly unions of original opposite pairs"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the sum of an actual subset S at coordinate i gives the indicator of e_i in S "
                    + "minus the indicator of minus e_i in S. Modulo three this vanishes exactly when the two "
                    + "membership bits agree. Thus S has coefficient-one sum zero if and only if there is a "
                    + "unique coordinate subset I for which S is the union of the original opposite pairs indexed "
                    + "by I."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "Good(w) requires nonzero sum on every nonempty proper contiguous interval. Only the full "
                    + "word is exempt, even when its sum is zero. The equivalent decomposition predicate "
                    + "quantifies over actual decompositions w = l ++ u ++ v, with u nonempty and at least one of "
                    + "l or v nonempty. This spectrum supplies no count of Good orders by itself. The paired "
                    + "Good-order enumeration corresponds to known connected chord diagrams; no "
                    + "literature-priority claim or solution of the arbitrary-subset sequenceability problem "
                    + "follows.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "r",
                C("Nat"),
                A(
                    "S",
                    C("Finset", C("V", FormulaDsl.Id("r"))),
                    Imp(
                        new Formula.Relation(
                            FormulaDsl.Id("S"),
                            FormulaRelationOperator.SubsetOf,
                            C("alphabet", FormulaDsl.Id("r"))
                        ),
                        IffR(
                            E(C("sum", FormulaDsl.Id("S")), D(0)),
                            Ex(
                                "I",
                                C("Finset", C("Fin", FormulaDsl.Id("r"))),
                                AndR(
                                    E(FormulaDsl.Id("S"), C("pairs", FormulaDsl.Id("I"))),
                                    A(
                                        "J",
                                        C("Finset", C("Fin", FormulaDsl.Id("r"))),
                                        Imp(
                                            E(FormulaDsl.Id("S"), C("pairs", FormulaDsl.Id("J"))),
                                            E(FormulaDsl.Id("J"), FormulaDsl.Id("I"))
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula E(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula IffR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Iff, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
}
