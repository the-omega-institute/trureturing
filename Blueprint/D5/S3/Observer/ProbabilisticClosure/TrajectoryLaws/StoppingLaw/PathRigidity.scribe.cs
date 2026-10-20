using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw;

internal sealed class PathRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix probabilities reconstruct a detached consecutive path", H("Prefix probabilities reconstruct a detached consecutive path"), Blocks(
            Paragraph(Text("Bias consists of a real parameter p strictly between zero and one and different from one half. Its spin masses are pi(false)=1-p and pi(true)=p. Write T(n)=(1-p)^n+p^n and d(n)=T(n)-T(n+1). All finite-spin probabilities refer to one common iid assignment on the finite integer window V.")),
            Paragraph(Text("pathEdges(L,n) is the integer interval from L to L+n-1 and pathVertices(L,n) runs from L to L+n. zeroEdges(E) says that both endpoint spins of every edge in E agree. SupportsEdges requires both endpoints of every listed edge to lie in V. PrefixMasses means that every nonempty prefix of length r has zero-edge probability T(r+1).")),
            Describe.Lean(DescribeId.Create("prefixes-force-consecutive"), DeclarationHandle.Create(Prefix + "prefixes_force_consecutive"),
                H("Every new edge extends an endpoint"), StatementSource.FromAuthor(Disp(All("beta", N("Bias"), All("V", A("Finset", N("Int")), All("es", A("List", N("Int")), Imp(Conj(A("SupportsEdges", N("V"), N("es")), A("PrefixMasses", N("beta"), N("V"), N("es")), Leq(D(1), A("length", N("es")))), Conj(A("Nodup", N("es")), Some("L", N("Int"), Equal(A("toFinset", N("es")), A("pathEdges", N("L"), A("length", N("es")))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction appends one edge at a time. A repeated edge retains the old prefix mass. A detached edge gives a strictly different factorized mass. Both alternatives contradict the prescribed next prefix mass, leaving exactly the two adjacent endpoint extensions. Query order need not be monotone."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-path-geometry"), DeclarationHandle.Create(Prefix + "finite_path_geometry"),
                H("Joint masses also separate the target vertex"), StatementSource.FromAuthor(Disp(All("beta", N("Bias"), All("V", A("Finset", N("Int")), All("es", A("List", N("Int")), All("q", N("Int"), Imp(Conj(Leq(D(1), A("length", N("es"))), A("SupportsEdges", N("V"), N("es")), A("PrefixMasses", N("beta"), N("V"), N("es")), All("s", N("Bool"), Equal(A("prob", N("beta"), N("V"), A("inter", A("zeroEdges", A("toFinset", N("es"))), A("spinEvent", N("q"), N("s")))), TimesOf(A("pi", N("beta"), N("s")), A("T", N("beta"), PlusOf(A("length", N("es")), D(1))))))), Conj(A("Nodup", N("es")), Some("L", N("Int"), Conj(Equal(A("toFinset", N("es")), A("pathEdges", N("L"), A("length", N("es")))), A("notMem", N("q"), A("pathVertices", N("L"), A("length", N("es")))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("spinEvent(q,s) is the set of source spins with S(q)=s. If q lay on the recovered path, the two conditional zero-prefix probabilities would force (1-p)^n=p^n for positive n. The biased interior parameter excludes this equality. Both target-spin sections are required."))), DescribeRole.Theorem),
            Paragraph(Text("The finite product factorizations concern the same source realization. Positivity and strict mass gaps hold for every permitted bias; no numerical approximation is used.")))));
    private static Formula N(string name) => F.Seq(Operatorname, Grp(F.Id(name)));
    private static Formula A(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.Add(F.Seq(Comma, Sp));
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return F.Seq(parts.ToArray());
    }
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(Forall, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula Some(string name, Formula type, Formula body) =>
        F.Seq(Exists, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula Equal(Formula x, Formula y) => F.Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => F.Seq(x, Sp, Le, Sp, y);
    private static Formula Imp(Formula x, Formula y) => F.Seq(Open, x, Close, Sp, To, Sp, Open, y, Close);
    private static Formula PlusOf(Formula x, Formula y) => F.Seq(Open, x, Sp, Plus, Sp, y, Close);
    private static Formula TimesOf(Formula x, Formula y) => F.Seq(Open, x, Sp, Star, Sp, y, Close);
    private static Formula Conj(params Formula[] xs)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) parts.Add(F.Seq(Sp, Land, Sp));
            parts.Add(F.Seq(Open, xs[i], Close));
        }
        return F.Seq(parts.ToArray());
    }
}
