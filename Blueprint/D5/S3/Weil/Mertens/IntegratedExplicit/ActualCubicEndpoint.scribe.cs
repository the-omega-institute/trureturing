using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualCubicEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic resolvent bounds at the actual spectral endpoint",
        H("Cubic resolvent bounds at the actual spectral endpoint"),
        Blocks(
            Describe.Lean(DescribeId.Create("resolvent-mode-sharp-norm"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint.resolventMode_norm_le"),
                H("A single resolvent mode"), StatementSource.FromAuthor(ModeClaim()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative Laplace variable s, the norm of s+1-z "
                    + "is at least the norm of 1-z when Re(z) <= 1. The exponential norm factors "
                    + "into the decay at the endpoint b and exp(-s*b). Integrating the remaining "
                    + "Laplace polynomial gives the original weight W(b)=(b+2)/b^3."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-spectral-tail-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint.actual_spectral_tail_bound"),
                H("The finite-height split"), StatementSource.FromAuthor(TailClaim()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write rho(k) for the actual zero at occurrence k. The set L(T) "
                        + "contains every k with abs(Im(rho(k))) <= T. Both ordinate signs and all "
                        + "analytic multiplicities are included. The mass C3(T) sums inverse cubes "
                        + "of the absolute ordinate over L(T). The mass C2(T) sums inverse squares "
                        + "over its complement. S is the complete actual spectrum and M is the existing first Li mass.")),
                    Paragraph(Text("The coefficient contributes one denominator from rho(k) and "
                        + "one from 1-rho(k). The mode contributes another denominator from "
                        + "1-rho(k). Each denominator is bounded below by the absolute ordinate. "
                        + "Reciprocal-square summability proves L(T) finite and permits the "
                        + "countable resolvent sum to split at T. The critical-line premise gives "
                        + "exp(-b/2) on L(T). Above T, strip membership bounds the exponential "
                        + "by one, and the third inverse ordinate is bounded by 1/T."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Positive(Formula a) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);

    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula ModeClaim()
    {
        var z = F.Id("z");
        var b = F.Id("b");
        var realPart = Call("Re", z);
        var difference = Subtract(D(1), z);
        var nonzero = new Formula.Relation(difference, FormulaRelationOperator.NotEqual, D(0));
        var decay = Call("exp", Multiply(Seq(Open, Subtract(realPart, D(1)), Close), b));
        var bound = new Formula.Fraction(Multiply(Call("W", b), decay),
            new Formula.Norm(difference));
        var endpoint = All("b", Real, Imp(Positive(b), Le(new Formula.Norm(Call("mode", z, b)), bound)));
        return Disp(All("z", Complex, Imp(Le(realPart, D(1)), Imp(nonzero, endpoint))));
    }

    private static Formula TailClaim()
    {
        var b = F.Id("b");
        var cutoff = F.Id("T");
        var k = F.Id("k");
        var low = Call("L", cutoff);
        var onLine = All("k", Natural, Imp(
            new Formula.Relation(k, FormulaRelationOperator.MemberOf, low),
            new Formula.Relation(Call("Re", Call("rho", k)), FormulaRelationOperator.Equal,
                new Formula.Fraction(D(1), D(2)))));
        var criticalDecay = Call("exp", new Formula.Fraction(new Formula.Negate(b), D(2)));
        var highMass = Call("C2", cutoff);
        var total = Add(Multiply(criticalDecay, Call("C3", cutoff)),
            new Formula.Fraction(highMass, cutoff));
        var tailBound = Le(new Formula.Norm(Call("spectralTail", F.Id("S"), b)),
            Multiply(Call("W", b), Seq(Open, total, Close)));
        var fullMass = Multiply(new Formula.Fraction(Seq(D(1), D(0), D(1)),
            Seq(D(1), D(0), D(0))), F.Id("M"));
        var conclusion = And(Call("Finite", low), And(tailBound, Le(highMass, fullMass)));
        var statement = Imp(Positive(b), Imp(Positive(cutoff), Imp(onLine, conclusion)));
        return Disp(All("b", Real, All("T", Real, statement)));
    }
}
