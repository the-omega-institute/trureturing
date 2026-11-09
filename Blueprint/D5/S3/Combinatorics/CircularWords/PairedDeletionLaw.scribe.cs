using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class PairedDeletionLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two overlapping paired deletion channels from the same original cycle determine every finite signed law, and therefore every probability law, on the complete fixed-support carrier.",
        H("Law Identification from Two Overlapping Paired Deletions"), Blocks(
            Paragraph(Text("Fix a finite support A with at least four labels and distinct supported labels a, b, c. "
                + "The two channels are F(C)=(D_a(C),D_b(C)) and G(C)=(D_b(C),D_c(C)); each pair is produced by the same source cycle. "
                + "Rotations are identified and reversal remains distinct. In the displayed formulas, Weights(I) denotes I -> Real, pairedPushforward(a,b,X,w) is the pushforward of w through i -> (D_a(X(i)),D_b(X(i))). Probability weights are nonnegative and have total mass one.")),
            Describe.Lean(DescribeId.Create("signed-law-identification"),
                DeclarationHandle.Create(Prefix + "signed_injective"),
                H("Signed law identification on every finite legal realization"),
                StatementSource.FromAuthor(SignedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite injective legal realization of the fixed-support cycles, equality of the two F pushforwards and equality of the two G pushforwards imply equality of the real signed weights. The proof uses the exact two-element R1 fibre classification: a non-singleton F fibre has a G-leaf, and the analogous statement holds with F and G exchanged.")),
            Paragraph(Text("FixedCycles(A) is the subtype of all nodup directed cycles C with toFinset(C)=A, modulo rotation only. The declarations fixedCycles_finite and fixedCyclesFintype supply its finite enumeration, and fixedCycles_nonempty supplies an actual legal original. In signed_injective take I=FixedCycles(A), X=Subtype.val, hi=Subtype.val_injective, hn(C)=C.property.1 and hs(C)=C.property.2. Its two channel hypotheses are exactly equality of the separate F and G pushforwards on this complete carrier. Thus all real signed source weights are identified, including nonnegative weights with total mass one. This is a direct application of the displayed theorem.")),
            Paragraph(Text("For native probability laws mu and nu on FixedCycles(A), use the discrete measurable structures and give each readout its finite range. The range-valued maps actualF(C) and actualG(C) contain the actual pairs F(C) and G(C), respectively; their value maps are injective, so restricting the codomains to these ranges preserves equality of the native readout laws. By massVector_map, equality of mu.map(actualF) and nu.map(actualF), and separately of mu.map(actualG) and nu.map(actualG), gives equality of the corresponding pushMass coordinates. A range coordinate is exactly the signed pushforward fibre sum, and every output outside the range has zero mass. Applying signed_injective with the same subtype parameters identifies massVector(mu) and massVector(nu); massVector_injective then gives mu=nu. The two pair laws are supplied separately; no joint (F,G) law is assumed. This derivation applies for arbitrary ambient DecidableEq labels and includes support size four.")),
            Paragraph(Text("A single paired channel can retain the adjacent-swap ambiguity classified in PairedDeletionFiber. The overlap through b supplies the singleton leaf that removes that ambiguity. No reversal quotient, abstract forest hypothesis, or three independent marginal law assumption is used."))),
                DescribeRole.Theorem))));

    // pairedPushforward(a,b,X,w) means pushforward(i => paired(a,b,X(i)),w).
    // Weights(I) is the function type I -> Real; Function is used as type notation.
    private static Formula SignedFormula()
    {
        Formula i = F.Id("i"), x = F.Id("X"), mu = F.Id("mu"), nu = F.Id("nu");
        Formula legal = All("i", F.Id("I"), And(Call("Nodup", Call("X", i)),
            Eq(Call("toFinset", Call("X", i)), F.Id("A"))));
        Formula conclusion = Imp(And(CommonPremise(), And(Call("Injective", x),
            And(legal, ChannelEquality(x, mu, nu)))), Eq(mu, nu));
        Formula body = All("I", Call("Type"),
            Seq(OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
                All("X", Call("Function", F.Id("I"), Call("Cycle", F.Id("T"))),
                    All("mu", Call("Weights", F.Id("I")),
                        All("nu", Call("Weights", F.Id("I")), conclusion)))));
        return QuantifySupport(body);
    }

    private static Formula ChannelEquality(Formula x, Formula mu, Formula nu) => And(
        Eq(Call("pairedPushforward", F.Id("a"), F.Id("b"), x, mu),
            Call("pairedPushforward", F.Id("a"), F.Id("b"), x, nu)),
        Eq(Call("pairedPushforward", F.Id("b"), F.Id("c"), x, mu),
            Call("pairedPushforward", F.Id("b"), F.Id("c"), x, nu)));

    private static Formula CommonPremise() => And(
        new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, Call("card", F.Id("A"))),
        And(In(F.Id("a"), F.Id("A")), And(In(F.Id("b"), F.Id("A")),
            And(In(F.Id("c"), F.Id("A")), And(Ne(F.Id("a"), F.Id("b")),
                And(Ne(F.Id("b"), F.Id("c")), Ne(F.Id("a"), F.Id("c"))))))));

    private static Formula QuantifySupport(Formula body) => Disp(All("T", Call("Type"),
        Seq(OpenBracket, Call("DecidableEq", F.Id("T")), CloseBracket, Sp,
            All("A", Call("Finset", F.Id("T")), All("a", F.Id("T"),
                All("b", F.Id("T"), All("c", F.Id("T"), body)))))));

    private static Formula In(Formula a, Formula set) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, set);
    private static Formula Ne(Formula a, Formula b) => new Formula.Not(Seq(Open, Eq(a, b), Close));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
