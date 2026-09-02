using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyRationalGeneratingFunctionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite exponential moment sequence has the expected finite rational "
            + "generating function on its common disk of convergence.",
        H("Finite Prony Rational Generating Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-rational-generating-function"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/"
                        + "FinitePronyRationalGeneratingFunction."
                        + "finite_prony_rational_generating_function"),
                H("Finite Prony moments sum to their rational resolvents"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely many complex nodes q_j and weights m_j, define the nth "
                            + "moment c_n as the sum of m_j q_j^n. The named predicate "
                            + "finitePronyConvergesAt records that every geometric mode q_j z "
                            + "has norm below one.")),
                    Paragraph(Text(
                        "The Lean proof is separated into three machine-checkable layers. A "
                            + "single mode is summed with Mathlib's geometric-series HasSum "
                            + "theorem, the finite family is combined with hasSum_sum, and the "
                            + "result is exposed through the named generating-series and "
                            + "rational-function interfaces.")),
                    Paragraph(Text(
                        "On the common convergence disk, finitePronyGeneratingSeries equals "
                            + "finitePronyRationalFunction. This is the analytic bridge from "
                            + "finite exponential moments to a rational transfer function.")),
                    Paragraph(Text(
                        "The theorem is pointwise on the common disk of convergence. It does "
                            + "not recover unknown nodes, quantify numerical conditioning, "
                            + "handle repeated confluent modes, or construct an infinite "
                            + "Hankel operator."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula nodes = F.Id("q");
        Formula weights = F.Id("m");
        Formula point = F.Id("z");

        return Disp(Seq(
            Forall, Sp, nodes, Comma, Sp, weights, Comma, Sp, point, Comma, Sp,
            Call("finitePronyConvergesAt", nodes, point), Sp, Rightarrow, Sp,
            Call("finitePronyGeneratingSeries", nodes, weights, point),
            Sp, Eq, Sp,
            Call("finitePronyRationalFunction", nodes, weights, point), Dot));
    }
}
