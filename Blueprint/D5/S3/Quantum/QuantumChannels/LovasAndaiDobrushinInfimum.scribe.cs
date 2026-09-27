using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class LovasAndaiDobrushinInfimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/lovas2016volume");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A qubit channel lies over a classical channel when the images of the two basis projections have the prescribed diagonal entries. Over the classical channel with parameters a and f, the trace-distance contraction coefficient of every such qubit channel is at least |a - f|, and a measure-and-prepare channel attains this value.",
        H("The least trace-distance contraction coefficient over a classical channel"),
        Blocks(
            DefinitionNode("classicalFiber", "Qubit channels over a classical channel", FiberFormula(),
                "In the parametrization of Lovas and Andai the Choi blocks Q_11 and Q_22 are the images of the projections onto the first and the second basis vector, with diagonals (a, 1 - a) and (f, 1 - f). The set collects the completely positive trace-preserving qubit maps with these diagonal entries."),
            DefinitionNode("dobrushin", "The trace-distance contraction coefficient", DobrushinFormula(),
                "The supremum, over all pairs of qubit states, of the ratio between the trace norm Tr|Q(rho) - Q(sigma)| of the difference of the images and the trace norm Tr|rho - sigma| of the difference of the states; a pair with rho = sigma contributes 0/0, which is 0 in Lean."),
            DefinitionNode("claim", "The Lovas-Andai conjecture", ClaimDefinitionFormula(),
                "For all parameters a and f in the unit interval, |a - f| is the least value of the contraction coefficient over the qubit channels above the classical channel; in particular the infimum equals |a - f| and is attained."),
            TheoremNode("result", "The infimum is |a - f| and is attained", ClaimFormula(),
                "Lower bound: for a channel Q over the classical channel, the images of the two basis projections differ by a matrix whose upper-left entry is a - f and, by trace preservation, whose lower-right entry is f - a. Testing the variational formula for the trace norm with the unitary diag(s, -s), where s is the sign of a - f, bounds that trace norm below by 2|a - f|, while the trace norm of the difference of the two projections is 2; so the ratio for this pair, and hence the coefficient, is at least |a - f|. Attainment: the measure-and-prepare channel with Kraus operators sqrt(p_j(i)) |i><j|, where p_0 = (a, 1 - a) and p_1 = (f, 1 - f), lies over the classical channel. It sends the difference of two states rho and sigma to the diagonal matrix with entries (a - f)t and (f - a)t, where t = rho_00 - sigma_00. Every unitary has diagonal entries of modulus at most one, so the variational formula bounds the trace norm of the image by 2|a - f||t|, while the same test unitary as before bounds the trace norm of rho - sigma below by 2|t|. Hence every ratio is at most |a - f|.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("lovas-andai-2016-dobrushin-infimum"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock DefinitionNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("lovas-andai-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock TheoremNode(string name, string title, Formula formula, string prose,
        OpenProblemResolutionClaim? resolution) =>
        Describe.Lean(DescribeId.Create("lovas-andai-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            resolution);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Qubit() => Call("Fin", D(2));
    private static Formula Channels() => Call("QuantumChannel", Qubit(), Qubit());
    private static Formula States() => Call("DensityState", Qubit());
    private static Formula Projection(byte i) => Call("Matrix.single", D(i), D(i), D(1));
    private static Formula Entry(Formula matrix, byte i) => new Formula.Apply(matrix, [D(i), D(i)]);

    private static Formula FiberFormula()
    {
        Formula a = F.Id("a"), f = F.Id("f"), q = F.Id("Q");
        Formula first = Parenthesized(Call("act", q, Projection(0)));
        Formula second = Parenthesized(Call("act", q, Projection(1)));
        Formula condition = And(And(Equal(Entry(first, 0), a), Equal(Entry(first, 1), Subtract(D(1), a))),
            And(Equal(Entry(second, 0), f), Equal(Entry(second, 1), Subtract(D(1), f))));
        Formula fiber = Seq(OpenBrace, Member(q, Channels()), Sp, Mid, Sp, condition, CloseBrace);
        return Disp(All("a", Reals(), All("f", Reals(), Equal(Call("classicalFiber", a, f), fiber))));
    }

    private static Formula DobrushinFormula()
    {
        Formula q = F.Id("Q"), x = F.Id("x"), rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula ratio = new Formula.Fraction(
            Call("traceNorm", Subtract(Call("Q.mapState", rho), Call("Q.mapState", sigma))),
            Call("traceNorm", Subtract(rho, sigma)));
        Formula ratios = Seq(OpenBrace, Member(x, Reals()), Sp, Mid, Sp,
            Some("rho", States(), Some("sigma", States(), Equal(x, ratio))), CloseBrace);
        return Disp(All("Q", Channels(), Equal(Call("dobrushin", q), Call("sSup", ratios))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("a"), f = F.Id("f");
        Formula unit = Seq(OpenBracket, D(0), Comma, Sp, D(1), CloseBracket);
        Formula image = Call("Set.image", Named("dobrushin"), Call("classicalFiber", a, f));
        Formula least = Call("IsLeast", image, new Formula.Absolute(Subtract(a, f)));
        return All("a", Reals(), All("f", Reals(),
            Implies(And(Member(a, unit), Member(f, unit)), least)));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(ClaimBody());
}
