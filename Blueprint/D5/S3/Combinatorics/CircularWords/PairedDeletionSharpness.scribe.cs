using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class PairedDeletionSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/PairedDeletionSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite support with at least four labels and every three distinct supported labels, native real probability laws on actual cycles attain source total variation one and paired-deletion readout total variations one third on each of two overlapping channels.",
        H("Sharpness of Overlapping Paired-Deletion Stability"), Blocks(
            Paragraph(Text("For every finite support with at least four labels and every three distinct supported labels a, b, c, there are two genuine probability measures on legal oriented cycles whose source total variation is one while the two overlapping paired-deletion readouts (D_a,D_b) and (D_b,D_c) each retain total variation exactly one third. The construction is carried by six actual rotation classes.")),
            Describe.Lean(DescribeId.Create("real-paired-deletion-sharpness"),
                DeclarationHandle.Create(Prefix + "real_probability_paired_deletion_sharpness"),
                H("Native real-law sharpness and coefficient obstructions"),
                StatementSource.FromAuthor(NativeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose the six actual cycles C=[a,b,c,L], CF=[b,a,c,L], CG=[a,c,b,L], E=[c,b,a,L], EF=[c,a,b,L], and EG=[b,c,a,L]. The first law puts mass one third on CF, CG, and E; the second puts mass one third on C, EF, and EG. A rooted insertion argument proves that these are six distinct rotation classes and that every class has support exactly A.")),
                    Paragraph(Text("For F=(D_a,D_b), the pairs from CF and C coincide, as do the pairs from E and EF; after cancellation the signed difference is a dipole of two distinct output atoms with weights plus or minus one third. The same calculation for G=(D_b,D_c) cancels CG with C and E with EG. Substitution into a universal sum or maximum inverse inequality gives K at least 3/2 or 3.")),
                    Paragraph(Text("The theorem uses native ProbabilityMeasure values and the repository's real finite half-l1 total variation. In the formula, Source(a,b,c,L) is the set of the six displayed cycle classes, sourceCycle enumerates them, muMass and nuMass are the specified one-third weights, and fChannel and gChannel are the actual pair maps into their finite realized output ranges. All finite carriers have their discrete measurable structures. The formula states the existing native-real theorem, including its listing, legality, injectivity, mass, and coefficient conclusions.")))),
            Paragraph(Text("For the full fixed-support carrier FixedCycles(A), include each witness cycle by its actual rotation class and extend both masses by zero outside the six-cycle image. The source inclusion and the induced inclusions of both output carriers are injective, and the channel squares commute. Native massVector/map correspondence, pushforward composition and invariance of finite half-l1 total variation under injections preserve all three values: 1, 1/3, 1/3. Hence any universal sum coefficient for all native probability laws on FixedCycles(A) is at least 3/2, and any universal maximum coefficient is at least 3.")),
            Paragraph(Text("The actual paired-deletion fibre classification supplies opposite-channel singleton leaves in both orientations on the complete legal carrier. Applying LocalLeafInverse.total_variation_le_sum and LocalLeafInverse.total_variation_le_max to those actual channels gives matching upper coefficients 3/2 and 3. These are therefore the optimal constants for the sum and maximum of the two separate observed total-variation errors, for every A, a, b, c under the stated support and distinctness assumptions.")),
            Paragraph(Text("The proof has standard kernel axiom closure only: propext, Classical.choice, and Quot.sound.")))));

    // The current pinned corpus has no entry for this existing native theorem.
    // Use the ordinary authored-presentation interface, retaining its exact Lean
    // handle and the automatically recorded projection gap. No fixture is patched.
    private static Formula NativeStatement()
    {
        var source = Spec("Source");
        var laws = Call("ProbabilityMeasure", source);
        var legal = All("C", source, And(
            Call("Nodup", Call("val", I("C"))),
            Eq(Call("toFinset", Call("val", I("C"))), I("A"))));
        var masses = And(
            Eq(Mass(I("rho")), Spec("muMass")),
            Eq(Mass(I("sigma")), Spec("nuMass")),
            Eq(SourceTv(I("rho"), I("sigma")), D(1)),
            Eq(ObservedTv("fChannel", I("rho"), I("sigma")), Third()),
            Eq(ObservedTv("gChannel", I("rho"), I("sigma")), Third()),
            Coefficient(false, laws), Coefficient(true, laws));
        var witnesses = Exists("rho", laws, Exists("sigma", laws, masses));
        var listing = Exists("L", Call("List", I("T")), And(
            Call("Nodup", I("L")),
            Eq(Call("toFinset", I("L")), Call("remainder", I("A"), I("a"), I("b"), I("c"))),
            Ne(I("L"), Call("nil")), legal, Call("Injective", Spec("sourceCycle")), witnesses));
        var premise = And(Leq(D(4), Call("card", I("A"))),
            In(I("a"), I("A")), In(I("b"), I("A")), In(I("c"), I("A")),
            Ne(I("a"), I("b")), Ne(I("a"), I("c")), Ne(I("b"), I("c")));
        var body = Imp(premise, listing);
        body = All("c", I("T"), body);
        body = All("b", I("T"), body);
        body = All("a", I("T"), body);
        body = All("A", Call("Finset", I("T")), body);
        body = Seq(OpenBracket, Call("DecidableEq", I("T")), CloseBracket, Sp, body);
        return Disp(All("T", Call("Type"), body));
    }

    private static Formula Coefficient(bool maximum, Formula laws)
    {
        var f = ObservedTv("fChannel", I("m"), I("n"));
        var g = ObservedTv("gChannel", I("m"), I("n"));
        Formula error = maximum ? Call("max", f, g) : Add(f, g);
        var estimate = Leq(SourceTv(I("m"), I("n")), Multiply(I("K"), error));
        var uniform = All("m", laws, All("n", laws, estimate));
        Formula lower = maximum ? D(3) : Seq(Frac, Grp(D(3)), Grp(D(2)));
        return All("K", Call("Real"), Imp(uniform, Leq(lower, I("K"))));
    }

    private static Formula Spec(string name) => Call(name, I("a"), I("b"), I("c"), I("L"));
    private static Formula Mass(Formula law) => Call("massVector", law);
    private static Formula SourceTv(Formula p, Formula q) => Call("TV", Mass(p), Mass(q));
    private static Formula ObservedTv(string channel, Formula p, Formula q) =>
        SourceTv(Call("map", p, Spec(channel)), Call("map", q, Spec(channel)));
    private static Formula Third() => Seq(Frac, Grp(D(1)), Grp(D(3)));
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Not(Seq(Open, Eq(a, b), Close));
    private static Formula And(params Formula[] values)
    {
        var body = values[^1];
        for (var i = values.Length - 2; i >= 0; --i)
            body = new Formula.Logic(Seq(Open, values[i], Close), FormulaLogicOperator.And,
                Seq(Open, body, Close));
        return body;
    }
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));

}
