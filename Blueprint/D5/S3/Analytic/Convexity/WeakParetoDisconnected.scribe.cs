using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class WeakParetoDisconnectedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Convexity/WeakParetoDisconnected.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/hieu2026connectedness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous convex objectives on a closed convex strip can have a disconnected weak Pareto solution set.",
        H("Hieu's Weak Pareto Connectedness Refutation"),
        Blocks(
            Entry("weak-pareto", "weakPareto", "Weak Pareto solutions", WeakPareto(),
                "In the Euclidean specialization E=EuclideanSpace ℝ (Fin n), weakPareto K f is a set of points in E. Membership means that the point is feasible and no feasible point is strictly smaller in every objective.",
                DescribeRole.Definition, true),
            Entry("connectedness-claim", "claim", "Connectedness for continuous convex data", Claim(),
                "Section 4.3 asks verbatim: “whether Sol^w(K,f) is still connected in the general convex case, with K closed convex and the f_i convex and continuous but not necessarily polynomial”. The paper adds: “no explicit example of a disconnected weak Pareto solution set is known” and says that Theorem 1 “shows that no such example can have convex polynomial data”. The formal claim quantifies over nonempty closed convex feasible sets in finite-dimensional Euclidean spaces of dimension at least one, at least one objective, continuous convex objectives, and preconnected weak Pareto solutions.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "A disconnected weak Pareto solution set", Disp(Seq(Neg, Sp, V("claim"))),
                "Take K=[0,∞)×[0,2], h(x)=√(x²+1)−x, f₁(x,y)=y², and f₂(x,y)=(max(h(x)−y/2,0))²−y/2. The Lean proof establishes nonemptiness, closedness and convexity of K, continuity and convexity of both objectives, weak Pareto boundary pieces y=0 and y≥2h(x), strict domination throughout 0<y<2h(x), and separation by the open sets y<h(x) and y>h(x). Thus the universal connectedness claim is false without boundedness or a constraint qualification.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hieu-2026-weak-pareto-connectedness"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Euclidean(string dimension) => Call("EuclideanSpace", Real, Call("Fin", V(dimension)));
    private static Formula SetOf(Formula carrier) => Call("Set", carrier);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, P(y));
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula WeakPareto()
    {
        Formula e = Euclidean("n");
        Formula k = V("K");
        Formula f = V("f");
        Formula point = V("z");
        Formula lhs = Call("At", f, V("i"), V("u"));
        Formula rhs = Call("At", f, V("i"), point);
        Formula less = new Formula.Relation(lhs, FormulaRelationOperator.LessThan, rhs);
        Formula all = All("i", Call("Fin", V("m")), less);
        Formula strictBody = new Formula.Logic(
            new Formula.Relation(V("u"), FormulaRelationOperator.MemberOf, k),
            FormulaLogicOperator.And, P(all));
        Formula strict = Seq(Exists, Sp, V("u"), Colon, Sp, e, Comma, Sp, strictBody);
        Formula body = Iff(
            new Formula.Relation(point, FormulaRelationOperator.MemberOf, Call("weakPareto", k, f)),
            new Formula.Logic(new Formula.Relation(point, FormulaRelationOperator.MemberOf, k),
                FormulaLogicOperator.And, Seq(Neg, Sp, P(strict))));
        Formula fType = Seq(Call("Fin", V("m")), Sp, Mapsto, Sp,
            Seq(e, Sp, Mapsto, Sp, Real));
        Formula quantified = All("n", Nat, All("m", Nat,
            All("K", SetOf(e), All("f", fType, All("z", e, body)))));
        return Disp(quantified);
    }

    private static Formula Claim()
    {
        Formula e = Euclidean("n");
        Formula k = SetOf(e);
        Formula f = Call("Fin", V("m"));
        Formula objectives = Seq(f, Sp, Mapsto, Sp, Seq(e, Sp, Mapsto, Sp, Real));
        Formula continuity = All("i", Call("Fin", V("m")),
            Call("Continuous", Call("At", V("f"), V("i"))));
        Formula convexity = All("i", Call("Fin", V("m")),
            Call("ConvexOn", Real, Call("univ"), Call("At", V("f"), V("i"))));
        Formula preconnected = Call("IsPreconnected",
            Call("weakPareto", V("K"), V("f")));
        Formula hypotheses = Imp(Call("Nonempty", V("K")),
            Imp(Call("IsClosed", V("K")),
                Imp(Call("Convex", Real, V("K")),
                    Imp(continuity, Imp(convexity, preconnected)))));
        Formula universals = All("n", Nat, All("m", Nat,
            Imp(Leq(D(1), V("n")), Imp(Leq(D(1), V("m")), All("K", k,
                All("f", objectives, hypotheses))))));
        return Disp(Iff(V("claim"), universals));
    }
}
