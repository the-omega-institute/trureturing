using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class LegalConditionedSeparationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under rational product window laws with every symbol mass at least a common positive rho, "
            + "different effective signatures have disagreement at least rho to the fifth power "
            + "after conditioning on exact seam legality.",
        H("Quantitative Teacher Separation under Legal Conditioning"),
        Blocks(
            Paragraph(Text("Input(n) is Fin(n) to the actual five windows 000,100,010,101,001, "
                + "written from low to high. Positions start at zero. Legal(x) uses the flattened-bit "
                + "Fibonacci predicate with false initial bit. All null positions and terminal null "
                + "windows remain present; there is no End query. A high bit and the following "
                + "window's low bit cannot both be true.")),
            Paragraph(Text("FiniteResponseLaw(Window) supplies an actual rational mass on every "
                + "one of the five windows, nonnegativity, and total mass one. laws(i) is the law "
                + "at position i. Before conditioning, independentSourceLaw(laws) assigns to x "
                + "the product of laws(i).mass(x(i)) over all positions. "
                + "legalNormalizer(laws) sums this product over precisely the Legal inputs. "
                + "conditionedDisagreement(laws,t,u) is the product mass of Legal inputs with "
                + "teacher(t,x) different from teacher(u,x), divided by that normalizer. "
                + "The source conditions the full product on all seams together. "
                + "It imposes no independence assumption after conditioning.")),
            Paragraph(Text("Roles(n) consists of strict triples p<q<r in Fin(n). "
                + "teacher(t,x) first tests high(x(p)) and low(x(q)), returning 1 when both hold. "
                + "Otherwise it tests high(x(q)) and low(x(r)), returning 2 when both hold, "
                + "and 0 otherwise. edge(i,j) is Some(i,j) when i+1<j, and None otherwise. "
                + "signature(t) is the ordered pair of its two effective edges. "
                + "Distinct signatures are a premise; distinct role triples alone are insufficient.")),
            Describe.Lean(DescribeId.Create("legal-conditioned-teacher-separation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/LegalConditionedSeparation.result"),
                H("Positive legal normalizer and a uniform fifth-power disagreement bound"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalizer is positive because the all-zero input "
                    + "is legal and has positive product mass. An active separating edge is "
                    + "forced by a high window at its first endpoint and a low window at its "
                    + "second endpoint. Zero windows immediately after the first endpoint and "
                    + "immediately before the second preserve every previously legal completion. "
                    + "At most one additional zero endpoint blocks a different active rival edge. "
                    + "The construction uses at most five positions, including overlaps only once. "
                    + "For equal first-edge signatures, the second-edge construction closes both "
                    + "first gates, preserving the actual priority rule. Each completable exterior "
                    + "therefore receives a fixed legal separating completion whose internal "
                    + "product mass is at least "
                    + "rho to the fifth power. Fiber normalization and the original product "
                    + "factorization yield the bound after legal conditioning. "
                    + "The exponent and constant have no optimality claim. "
                    + "A sample guarantee requires a separately specified sampling and label contract."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = V("n");
        var laws = V("laws");
        var rho = V("rho");
        var i = V("i");
        var a = V("a");
        var t = V("t");
        var u = V("u");
        var lawAt = new Formula.Apply(laws, [i]);
        var lower = All(i, Call("Fin", n), All(a, V("Window"),
            Seq(rho, Sp, Le, Sp, Call("mass", lawAt, a))));
        var signaturesDiffer = Seq(Call("signature", t), Sp, Neq, Sp, Call("signature", u));
        var conclusion = Seq(
            D(0), Sp, Lt, Sp, Call("legalNormalizer", laws), Sp, Land, Sp,
            Pow(rho, D(5)), Sp, Le, Sp, Call("conditionedDisagreement", laws, t, u));
        var roleClaim = All(t, Call("Roles", n), All(u, Call("Roles", n),
            Imp(signaturesDiffer, conclusion)));
        var lawType = Seq(Call("Fin", n), Sp, To, Sp, Call("FiniteResponseLaw", V("Window")));
        return All(n, Seq(Mathbb, Grp(V("N"))),
            All(laws, lawType, All(rho, Seq(Mathbb, Grp(V("Q"))),
                Imp(Seq(D(0), Sp, Lt, Sp, rho), Imp(lower, roleClaim)))));
    }
}
