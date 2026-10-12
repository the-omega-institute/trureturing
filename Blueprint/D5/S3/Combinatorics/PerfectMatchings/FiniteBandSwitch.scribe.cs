using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class FiniteBandSwitchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RibbonEmbeddings/ghanbarisamal2026facial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual switch of two band pairs exchanges good and regular and yields equal expectations under an invariant finite law.",
        H("Band Switching and Expectation Symmetry"),
        Blocks(
            Paragraph(Text("Let X be a finite flag carrier. The permutations s and t are involutions "
                + "without fixed points, representing corner and band matchings. For four distinct points "
                + "a,b,t(a),t(b), let u swap t(a) and t(b), and let t'=u*t*u. "
                + "This replaces a--t(a), b--t(b) by a--t(b), b--t(a) and leaves all other pairs unchanged. "
                + "Good(s,t,a,b) means that a and b are in the same integer-power orbit of s*t. "
                + "Bad(s,t,a,b) means that s(a) and b are in the same such orbit. "
                + "Regular(s,t,a,b) means that neither orbit relation holds. "
                + "The two-matching connectivity theorem identifies Regular with distinct combinatorial boundary components.")),
            Describe.Lean(DescribeId.Create("band-switch"), DeclarationHandle.Create(Prefix + "band_switch"),
                H("Actual Band Surgery Exchanges the Categories"), StatementSource.FromAuthor(SwitchFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Delete the two selected band pairs by fixing their four endpoints. "
                    + "First-return paths in the remaining finite matching system construct a fixed-point-free endpoint pairing. "
                    + "Its value at one endpoint and involutivity force one of the three pairings of four points. "
                    + "The proved reattachment orbit formula then gives good-to-regular, regular-to-good, and bad-to-bad. "
                    + "The cut and both reattachments are explicitly identified with t and u*t*u; their orbit effect is not a premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the expectation statement, Omega is a nonempty finite set of equally weighted states. "
                + "The corner matching s is fixed and t(omega) is a fixed-point-free involutive band matching for every state. "
                + "The four marked points are distinct in every state. A state bijection tau satisfies "
                + "t(tau(omega)) = switch(t(omega),a,b) for each omega, where switch is the actual matching operation above. "
                + "MeanGood and MeanPhysicalRegular are the rational sums of the corresponding zero-one indicators "
                + "divided by card(Omega). PhysicalRegular is the negation of corner/band connectivity.")),
            Describe.Lean(DescribeId.Create("twist-expectation"),
                DeclarationHandle.Create(Prefix + "twist_invariant_uniform_expectation"),
                H("Equal Good and Regular Expectations Under the Stated Law"),
                StatementSource.FromAuthor(ExpectationFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Band surgery proves that a state's regular indicator equals the good indicator "
                    + "of its image under tau. Reindexing the finite sum gives equality of the two means. "
                    + "The statement makes the state-space and actual matching-transport assumptions explicit. "
                    + "It does not identify an unspecified distribution on unlabelled embeddings, prove surface realization, "
                    + "or imply exact thirds for any category."))), DescribeRole.Theorem))));

    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Matching(Formula p) => And(Call("Involutive", p), Call("FixedPointFree", p));
    private static Formula Type(string name, Formula t) => Call(name, V("s"), t, V("a"), V("b"));
    private static Formula Switched() => Call("switch", V("t"), V("a"), V("b"));
    private static Formula SwitchFormula() => Disp(All("X", V("FiniteType"),
        All("s", Call("Perm", V("X")), All("t", Call("Perm", V("X")),
        All("a", V("X"), All("b", V("X"),
            Imp(And(And(Matching(V("s")), Matching(V("t"))),
                Call("FourDistinct", V("a"), V("b"), Call("apply", V("t"), V("a")), Call("apply", V("t"), V("b")))),
                And(Iff(Type("Good", Switched()), Type("Regular", V("t"))),
                    And(Iff(Type("Bad", Switched()), Type("Bad", V("t"))),
                        Iff(Type("Regular", Switched()), Type("Good", V("t"))))))))))));
    private static Formula ExpectationFormula() => Disp(All("X", V("FiniteType"),
        All("Omega", V("NonemptyFiniteType"), All("s", Call("Perm", V("X")),
        All("t", Call("Function", V("Omega"), Call("Perm", V("X"))),
        All("tau", Call("Equiv", V("Omega"), V("Omega")),
        All("a", V("X"), All("b", V("X"),
            Imp(Call("ActualTwistFamily", V("s"), V("t"), V("tau"), V("a"), V("b")),
                Equal(Call("MeanGood", V("s"), V("t"), V("a"), V("b")),
                    Call("MeanPhysicalRegular", V("s"), V("t"), V("a"), V("b"))))))))))));
}
