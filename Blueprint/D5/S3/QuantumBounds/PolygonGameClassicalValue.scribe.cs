using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class PolygonGameClassicalValueDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumBounds/PolygonGameClassicalValue.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Resource/bulchandaniburnellsondhi2023polygon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every odd P at least three, the polygon game's optimal classical winning probability is one minus F(P minus one) divided by two to the power P.",
        H("The classical value of the odd polygon game"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-matching"),
                DeclarationHandle.Create(Module + "IsMatching"),
                H("Disjoint edges of a cycle"),
                StatementSource.FromAuthor(Disp(IsMatchingFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Edge i joins i to finRotate P i. A finite set M is a matching when it never contains both an edge and its cyclic successor. "
                    + "For P at least three this says precisely that no two selected edges share a vertex. "
                    + "Section 4.1, Rules of the polygon game (ArxivResub.tex, lines 636–658), indexes the polygon conditions by these matchings."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matching-input"),
                DeclarationHandle.Create(Module + "matchingInput"),
                H("The input covered by a matching"),
                StatementSource.FromAuthor(Disp(MatchingInputFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The input bit at i is true exactly when the edge starting at i or the edge ending at i belongs to M. "
                    + "This is the endpoint input specified in Section 4.1 (ArxivResub.tex, lines 653–655). "
                    + "The function is defined for every finite edge set, whether or not it is a matching."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wins"),
                DeclarationHandle.Create(Module + "wins"),
                H("All winning conditions"),
                StatementSource.FromAuthor(Disp(WinsFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A deterministic strategy s assigns a Boolean triple to each player and each Boolean input. "
                    + "The triple is associated to the right, so its coordinates are obtained by Prod.fst, Prod.fst after Prod.snd, and Prod.snd after Prod.snd. "
                    + "Each triple has even parity and the middle coordinates have even total parity. "
                    + "For every matching producing x, sum the first output at each selected edge's initial vertex, the third output at its terminal vertex, "
                    + "and the first output on input false at every uncovered vertex. This sum equals the matching's cardinality in ZMod 2. "
                    + "The empty, one-edge and two-edge matchings give Conditions 3, 4 and 5; larger matchings give Condition 6 "
                    + "(ArxivResub.tex, lines 629–655). Inputs coming from no matching retain the two parity conditions. "
                    + "The middle output is allowed to depend on the input, so both local response tables are included. "
                    + "Bool.toNat converts each bit to a natural number; every subsequent Nat.cast, including the cardinality cast, is displayed with its target type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("win-probability"),
                DeclarationHandle.Create(Module + "winProbability"),
                H("Uniform inputs and shared randomness"),
                StatementSource.FromAuthor(Disp(WinProbabilityFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each deterministic response table, count its winning inputs and divide by the number of all Boolean inputs, two to the power P. "
                    + "Weight this fraction by μ and sum over all response tables. When μ is nonnegative and sums to one, this is the classical winning probability "
                    + "with shared randomness and uniform inputs. The definition itself accepts arbitrary real weights. "
                    + "This is the winning probability used in Section 4.1, Classical winning probabilities (ArxivResub.tex, lines 684–717)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + "claim"),
                H("The Fibonacci value"),
                StatementSource.FromAuthor(Disp(Equal(Qualified("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every odd P at least three, every nonnegative normalized distribution on deterministic strategies has winning probability at most "
                    + "one minus F(P minus one) divided by two to the power P, and a deterministic strategy attains that value. "
                    + "Nat.fib has F(1) = F(2) = 1. The source gives the lower bound and conjectures its tightness "
                    + "(ArxivResub.tex, lines 703–717); the displayed proposition includes both the upper bound for shared randomness and an optimal deterministic strategy. "
                    + "The subtraction P minus one takes place in the natural numbers before applying Nat.fib, and the Fibonacci number is then cast to the reals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + "result"),
                H("The sharp upper bound"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix an odd P at least three and a deterministic strategy. If a local triple has odd parity for one input bit at one player, "
                        + "all inputs having that bit lose, accounting for half of all inputs. If a middle output changes with the input, "
                        + "flipping that player's input is an involution that changes the total middle parity by one. "
                        + "It injects winning inputs into losing inputs, so at least half of all inputs lose. "
                        + "If every middle output is constant but their sum is odd, every input loses. "
                        + "The fact that F(P minus one) is smaller than half of the two to the power P inputs covers all these cases.")),
                    Paragraph(Text(
                        "It remains to consider locally even triples with input-independent middle outputs bᵢ of even total parity. "
                        + "Write aᵢ and dᵢ for the first outputs on false and true, and cᵢ and eᵢ for the third outputs. "
                        + "Work in ZMod 2. Local parity gives cᵢ = aᵢ + bᵢ and eᵢ = dᵢ + bᵢ. "
                        + "Put A = Σᵢ aᵢ and tᵢ = aᵢ + dᵢ, and assign edge i the bit qᵢ = 1 + tᵢ + tᵢ₊₁ + bᵢ₊₁. "
                        + "Split the vertices into the initial and terminal vertices of M and its uncovered vertices. "
                        + "Substituting the local parity identities into the matching condition shows that it holds exactly when A + Σᵢ∈M qᵢ = 0. "
                        + "Thus this affine expression is the failure bit.")),
                    Paragraph(Text(
                        "Summing the edge bits around the cycle cancels each tᵢ twice. "
                        + "The remaining sum is P + Σᵢ bᵢ = 1, because P is odd and the middle parity is even. "
                        + "Hence some edge j has qⱼ = 1.")),
                    Paragraph(Text(
                        "Distinct matchings of an odd cycle have distinct endpoint inputs. Indeed, if M and N have the same covered vertices, "
                        + "let zᵢ be the integer difference of their edge indicators. At each vertex, equality of the covered-vertex indicators "
                        + "gives zᵢ + zᵢ₋₁ = 0, since a matching has at most one incident selected edge. "
                        + "The differences alternate in sign around the cycle; after the odd number P of steps, zᵢ equals its own negative. "
                        + "Every zᵢ is therefore zero, so M = N.")),
                    Paragraph(Text(
                        "Consider matchings N containing none of the three edges j minus one, j and j plus one. "
                        + "These are exactly the matchings disjoint from both endpoints of j. "
                        + "The remaining P minus two vertices form a path, with P minus three possible edges. "
                        + "Number those edges consecutively, starting two positions after j. Choosing a matching is equivalent to a Boolean word of length P minus three "
                        + "with no adjacent true bits. The count of such words is F(P minus one).")),
                    Paragraph(Text(
                        "For each such N, both N and N with j inserted are matchings. Their affine failure bits differ by qⱼ = 1, "
                        + "so at least one of their endpoint inputs loses. Choose N's input if it loses, and otherwise choose the input after insertion. "
                        + "This choice is injective: equal inputs on the same branch give equal matchings, and insertion can be reversed by removing j; "
                        + "inputs on opposite branches differ at vertex j. Thus at least F(P minus one) distinct inputs lose. "
                        + "Subtracting these losses from the two to the power P inputs and dividing by this positive denominator gives the deterministic upper bound.")),
                    Paragraph(Text(
                        "To attain the bound, index players from zero to P minus one. Every player except the last outputs (true, true, false) on both inputs; "
                        + "the last outputs (false, false, false) on false and (true, false, true) on true. "
                        + "This is the source's strategy (ArxivResub.tex, lines 703–706). "
                        + "All local triples are even, the middle outputs are fixed and have even total parity, and A = 0. "
                        + "Exactly the edge from the last player to the first has edge bit one. "
                        + "Consequently a losing input must come from a matching containing this edge. "
                        + "Removing that edge leaves a matching disjoint from its endpoints, so there are at most F(P minus one) losing inputs. "
                        + "The universal lower bound gives the reverse inequality, hence exactly that many losses and the stated winning fraction.")),
                    Paragraph(Text(
                        "Finally, the winning probability of a distribution is the finite weighted mean of the deterministic winning fractions. "
                        + "Nonnegative weights of total mass one preserve their common upper bound. "
                        + "Combining this upper bound with the deterministic strategy just described proves both parts of the proposition. "
                        + "The conclusion concerns uniform inputs and every odd P at least three; it makes no assertion about the quantum value, "
                        + "even polygons, or polygons inscribed in a larger game."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bulchandani-burnell-sondhi-2023-polygon-game-classical-value"),
                    ResolutionKind.Proved)))));

    private static Formula IsMatchingFormula() => All("P", Naturals(), All("M", EdgeSets(),
        IffOf(LocalCall("IsMatching", X("P"), X("M")),
            All("i", Players(), Imp(Member(X("i"), X("M")),
                new Formula.Not(Parenthesized(Member(Rotate(X("i")), X("M")))))))));

    private static Formula MatchingInputFormula() => All("P", Naturals(), All("M", EdgeSets(),
        Equal(LocalCall("matchingInput", X("P"), X("M")),
            LambdaOf("i", Players(), At(Qualified("decide"), Or(
                Member(X("i"), X("M")),
                Member(At(At(Qualified("Equiv", "symm"), At(Qualified("finRotate"), X("P"))), X("i")), X("M"))))))));

    private static Formula WinsFormula()
    {
        Formula output = At(X("s"), X("i"), At(X("x"), X("i")));
        Formula local = All("i", Players(), Equal(
            Add(Add(Bit(Fst(output)), Bit(Fst(Snd(output)))), Bit(Snd(Snd(output)))), Typed(D(0), Bits())));
        Formula middle = Equal(SumOver("i", Players(), Bit(Fst(Snd(output)))), Typed(D(0), Bits()));
        Formula endpoints = SumIn("i", X("M"), Add(
            Bit(Fst(At(X("s"), X("i"), Qualified("true")))),
            Bit(Snd(Snd(At(X("s"), Rotate(X("i")), Qualified("true")))))));
        Formula uncovered = Filter(Players(), LambdaOf("i", Players(),
            Equal(LocalCall("matchingInput", X("P"), X("M"), X("i")), Qualified("false"))));
        Formula rest = SumIn("i", uncovered, Bit(Fst(At(X("s"), X("i"), Qualified("false")))));
        Formula matchingRule = All("M", EdgeSets(), Imp(LocalCall("IsMatching", X("P"), X("M")),
            Imp(Equal(LocalCall("matchingInput", X("P"), X("M")), X("x")),
                Equal(Add(endpoints, rest), NatCast(At(Qualified("Finset", "card"), X("M")), Bits())))));
        return All("P", Naturals(), All("s", Strategies(), All("x", Inputs(),
            IffOf(LocalCall("wins", X("P"), X("s"), X("x")), And(local, And(middle, matchingRule))))));
    }

    private static Formula WinProbabilityFormula() => All("P", Naturals(), All("μ", Arrow(Strategies(), Reals()),
        Equal(LocalCall("winProbability", X("P"), Mu),
            SumOver("s", Strategies(), Fraction(Multiply(At(Mu, X("s")), RealWinningCount()), Denominator())))));

    private static Formula ClaimBody()
    {
        Formula upper = All("μ", Arrow(Strategies(), Reals()),
            Imp(All("s", Strategies(), LE(Typed(D(0), Reals()), At(Mu, X("s")))),
                Imp(Equal(SumOver("s", Strategies(), At(Mu, X("s"))), Typed(D(1), Reals())),
                    LE(LocalCall("winProbability", X("P"), Mu), Value()))));
        Formula attained = Some("s", Strategies(), Equal(Fraction(RealWinningCount(), Denominator()), Value()));
        return All("P", Naturals(), Imp(At(Qualified("Odd"), X("P")),
            Imp(LE(D(3), X("P")), And(upper, attained))));
    }

    private static Formula RealWinningCount() => NatCast(At(Qualified("Finset", "card"),
        Filter(Inputs(), LocalCall("wins", X("P"), X("s")))), Reals());
    private static Formula Denominator() => new Formula.Power(Typed(D(2), Reals()), X("P"));
    private static Formula Value() => Subtract(Typed(D(1), Reals()), Fraction(
        NatCast(At(Qualified("Nat", "fib"), Parenthesized(Subtract(X("P"), D(1)))), Reals()), Denominator()));
    private static Formula Players() => At(Qualified("Fin"), X("P"));
    private static Formula EdgeSets() => At(Qualified("Finset"), Players());
    private static Formula Inputs() => Arrow(Players(), Qualified("Bool"));
    private static Formula Strategies() => Arrow(Players(), Arrow(Qualified("Bool"),
        Parenthesized(Seq(Qualified("Bool"), Sp, Times, Sp,
            Parenthesized(Seq(Qualified("Bool"), Sp, Times, Sp, Qualified("Bool")))))));
    private static Formula Bits() => At(Qualified("ZMod"), D(2));
    private static Formula Rotate(Formula i) => At(Qualified("finRotate"), X("P"), i);
    private static Formula Fst(Formula pair) => At(Qualified("Prod", "fst"), pair);
    private static Formula Snd(Formula pair) => At(Qualified("Prod", "snd"), pair);
    private static Formula Bit(Formula bit) => NatCast(At(Qualified("Bool", "toNat"), bit), Bits());
    private static Formula NatCast(Formula value, Formula type) => Typed(At(Qualified("Nat", "cast"), value), type);
    private static Formula Filter(Formula type, Formula predicate) => At(Qualified("Finset", "filter"), predicate,
        Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), type)));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(X(name), set)), Sp, Parenthesized(body));
    private static Formula LocalCall(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula X(string name) => name == "μ" ? Mu : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
