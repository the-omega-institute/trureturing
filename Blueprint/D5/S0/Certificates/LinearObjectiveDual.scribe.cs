using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LinearObjectiveDualDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/LinearObjectiveDual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational primal and dual witnesses certify finite linear objective bounds and endpoint optimality.",
        H("Exact Rational Linear Objective Certificates"),
        Blocks(
            Paragraph(Text(
                "A feasible point satisfies a finite rational system A x less than or equal to b. A linear query is evaluated by an exact finite rational sum.")),
            Paragraph(Text(
                "An upper certificate is a nonnegative combination of constraint rows that represents the objective coefficients and whose weighted right-hand side is below the proposed upper value. A lower certificate applies the same construction to the negated objective.")),
            Paragraph(Text(
                "Weak duality proves universal validity. A feasible primal point with the same objective value upgrades validity to exact endpoint optimality. External optimization software may propose both witnesses, while Lean checks every coefficient, sign, sum, and equality.")),
            Describe.Lean(
                DescribeId.Create("upper-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "upper_bound_of_certificate"),
                H("A rational upper dual certificate proves a universal bound"),
                StatementSource.FromAuthor(UpperBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every feasible primal point, the nonnegative weighted constraint sum equals the objective and is bounded by the certificate right-hand side."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "lower_bound_of_certificate"),
                H("A rational lower dual certificate proves a universal bound"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The certificate represents the negated objective, so exact weak duality yields the claimed lower bound after reversing the sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-lower-bound-of-certificate-and-witness"),
                DeclarationHandle.Create(
                    Prefix + "exact_lower_bound_of_certificate_and_witness"),
                H("Matching rational dual and primal witnesses certify an exact lower endpoint"),
                StatementSource.FromAuthor(ExactLowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dual witness supplies universal validity and the primal witness supplies attainment at the same exact rational value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-upper-bound-of-certificate-and-witness"),
                DeclarationHandle.Create(
                    Prefix + "exact_upper_bound_of_certificate_and_witness"),
                H("Matching rational dual and primal witnesses certify an exact upper endpoint"),
                StatementSource.FromAuthor(ExactUpperFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem packages the proof obligation required for certified linear-program endpoint sharpness."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula UpperBoundFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula upper = F.Id("u");
        Formula point = F.Id("x");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            upper, Comma, Sp,
            Call("UpperBoundCertificate", rows, bounds, objective, upper), Sp,
            Rightarrow, Sp, Forall, Sp, point, Comma, Sp,
            Call("LinearFeasible", rows, bounds, point), Sp, Rightarrow, Sp,
            Call("linearObjective", objective, point), Sp, Le, Sp, upper, Dot));
    }

    private static Formula LowerBoundFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula lower = F.Id("l");
        Formula point = F.Id("x");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            lower, Comma, Sp,
            Call("LowerBoundCertificate", rows, bounds, objective, lower), Sp,
            Rightarrow, Sp, Forall, Sp, point, Comma, Sp,
            Call("LinearFeasible", rows, bounds, point), Sp, Rightarrow, Sp,
            lower, Sp, Le, Sp, Call("linearObjective", objective, point), Dot));
    }

    private static Formula ExactLowerFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula lower = F.Id("l");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            lower, Comma, Sp,
            Call("LowerBoundCertificate", rows, bounds, objective, lower), Sp,
            Rightarrow, Sp,
            Call("PrimalWitness", rows, bounds, objective, lower), Sp,
            Rightarrow, Sp,
            Call("IsExactLowerBound", rows, bounds, objective, lower), Dot));
    }

    private static Formula ExactUpperFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula upper = F.Id("u");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            upper, Comma, Sp,
            Call("UpperBoundCertificate", rows, bounds, objective, upper), Sp,
            Rightarrow, Sp,
            Call("PrimalWitness", rows, bounds, objective, upper), Sp,
            Rightarrow, Sp,
            Call("IsExactUpperBound", rows, bounds, objective, upper), Dot));
    }
}
