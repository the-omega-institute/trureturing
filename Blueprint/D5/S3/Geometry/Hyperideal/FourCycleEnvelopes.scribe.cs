using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleEnvelopesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison";
    private static readonly LibraryNoteRef Zhao =
        LibraryNoteRef.Create("D5/L/zhao2026cfmpincidence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed-coordinate monotonicity for the exact six-variable hyper-ideal cosine.",
        H("The shared mixed-coordinate comparison"),
        Blocks(
            Paragraph(Text("All variables below are real numbers. Icc(a,b) denotes the closed "
                + "interval [a,b]. In the local edge order (12,13,14,34,24,23), the inputs "
                + "(x,y,z,o,v,w) keep all six coordinates independent. Coordinates x and o "
                + "are opposite.")),
            Paragraph(Text("Define rad(x,y,z)=2xyz+x^2+y^2+z^2-1 and "
                + "P(x,y,z,o,v,w)=yz+vw+xyv+xzw-(x^2-1)o. The function cosine "
                + "is P divided first by sqrt(rad(x,y,w)) and then by sqrt(rad(x,z,v)). "
                + "This is the exact six-variable formula used by the cited source. "
                + "Both radicands are proved positive on the box.")),
            Describe.Lean(
                DescribeId.Create("hyperideal-mixed-coordinate-comparison"),
                DeclarationHandle.Create(Declaration),
                H("Increasing neighbours and decreasing the opposite coordinate"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromLiterature(Zhao),
                Blocks(
                    Paragraph(Text("All eleven variables lie in [1,2]. Increasing the four "
                        + "neighbouring coordinates and decreasing the opposite coordinate cannot "
                        + "decrease the actual cosine. The proof differentiates the original "
                        + "square-root expression and derives the nonnegative coupled numerator "
                        + "(x^2-1)(xow+xv+yo+yvw+z(1-w^2)). It retains endpoint continuity, "
                        + "positive denominators and the two actual tetrahedral symmetries.")),
                    Paragraph(Text("Endpoint envelopes used by later incidence arguments are "
                        + "obtained there by direct specialization and normalization. They are "
                        + "not separate formal declarations. Geometric identification with a "
                        + "tetrahedron, face-pairing topology and the global co-volume existence "
                        + "argument remain outside this analytic theorem."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        string[] names = ["x", "y", "z", "o", "v", "w", "Y", "Z", "O", "V", "W"];
        var a = names.Select(F.Id).ToArray();
        var intervals = a.Select(t => In(t, F.D(1), F.D(2))).ToArray();
        Formula[] orders = [Le(a[1], a[6]), Le(a[2], a[7]), Le(a[8], a[3]),
            Le(a[4], a[9]), Le(a[5], a[10])];
        return ForAll(names, Implies(And([.. intervals, .. orders]),
            Le(Call("cosine", a[0], a[1], a[2], a[3], a[4], a[5]),
               Call("cosine", a[0], a[6], a[7], a[8], a[9], a[10]))));
    }

    private static Formula ForAll(string[] names, Formula body)
    {
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = names.Select(name =>
            new Formula.BoundVariable(FormulaIdentifier.Create(name), real)).ToArray();
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);
    }

    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction.");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula In(Formula value, Formula lower, Formula upper) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, Call("Icc", lower, upper));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
