using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Resolution;

internal sealed class OpenPullbackObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Resolution/OpenPullbackObstruction.";
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Inst(string n) => Seq(OpenBracket, Call(n, V("E")), CloseBracket, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every preselected compact Hausdorff zero-dimensional resolution of the Cantor square is defeated by a later binary-coordinate extension on its entire pullback.",
        H("Universal obstruction to preselected full-pullback compatibility"),
        Blocks(
            Paragraph(Text(
                "Cantor is literally Nat to Bool with the product topology; I is the closed real unit interval with its usual subspace topology. "
                + "Square is Cantor times I. The type E has arbitrary universe and weight. Its only topological assumptions are compactness, "
                + "Hausdorffness and total disconnectedness, which in this compact Hausdorff setting gives a clopen basis. "
                + "The given a:E to Square is continuous and surjective. Openness of the first coordinate of a is not assumed.")),
            Describe.Lean(
                DescribeId.Create("closed-section-boundary"),
                DeclarationHandle.Create(Owner + "exists_nonopen_section"),
                H("Constructed continuous section with a nonopen incidence set"),
                StatementSource.FromAuthor(Disp(Seq(
                    All("K", Call("Set", V("Square"))), Call("IsClosed", V("K")), Sp, Land, Sp,
                    Call("Member", Call("pair", V("star"), V("zero")), V("K")), Sp, Land, Sp,
                    Neg, Sp, Call("Member", Call("pair", V("star"), V("one")), V("K")), Sp, Rightarrow, Sp,
                    Exists, Sp, V("s"), Colon, Sp, Fn(V("Cantor"), V("I")), Comma, Sp,
                    Call("Continuous", V("s")), Sp, Land, Sp,
                    Call("IsClosed", Call("Incidence", V("K"), V("s"))), Sp, Land, Sp,
                    Neg, Sp, Call("IsOpen", Call("Incidence", V("K"), V("s")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "star is the all-false sequence, and Incidence(K,s)=D={b:(b,s(b)) belongs to K}. The compact vertical section at star "
                    + "has a maximum c<1. Set x(n)=c+(1-c)/(n+2); these actual interval points are above c and converge to c. "
                    + "The open neighborhood U(n) consists of b with (b,x(n)) outside K. Choose a cylinder length m(n) contained in U(n). "
                    + "Recursively k(0)=0 and k(n+1)=max(k(n),m(n))+1. Let V(n) be the cylinder of all-false coordinates below k(n). "
                    + "Flipping the coordinate max(k(n),m(n)) gives b(n) in U(n) and V(n), outside V(n+1), with b(n) converging to star. "
                    + "Every other binary sequence escapes some V(n+1); its first escape defines its annulus. Put s=x(n) there and s(star)=c. "
                    + "Clopen annuli give continuity away from star, and the convergent tail on V(N) gives continuity at star. "
                    + "The continuous graph makes D closed. It contains star and misses every b(n), proving that it is not open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-preselected-resolution"),
                DeclarationHandle.Create(Owner + "exists_obstruction"),
                H("Complete arbitrary-weight full-pullback obstruction"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(All("E", Seq(V("Type"), Underscore, Grp(V("u")))), Inst("TopologicalSpace"),
                        Inst("CompactSpace"), Inst("TTwoSpace"), Inst("TotallyDisconnectedSpace")),
                    Seq(All("a", Fn(V("E"), V("Square"))), Call("Continuous", V("a")), Sp, Land, Sp,
                        Call("Surjective", V("a")), Sp, Rightarrow),
                    Seq(Exists, Sp, V("s"), Colon, Sp, Fn(V("Cantor"), V("I")), Comma, Sp,
                        Call("Construction", V("a"), V("s")))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Construction is the full Lean certificate. T=Square disjoint-sum Cantor has its usual sum topology. "
                        + "The map f=forget(s) is identity on the left summand and b mapped to (b,s(b)) on the right. "
                        + "The map p=base is the product first projection on the left and identity on the right. It is continuous, open and onto. "
                        + "The forgetting map is continuous and onto, lies over p, and each of its fibers has cardinality at most two; "
                        + "this bound is on f, not on p.")),
                    Paragraph(Text(
                        "The actual binary map sends the left summand to ((b,x),false) and the right to ((b,s(b)),true). "
                        + "It is a closed embedding, its range is exactly {(z,j):j=false or (j=true and z.second=s(z.first))}, "
                        + "and forgetting its Bool coordinate gives f. Thus T is compact metrizable and has the stated genuine binary realization.")),
                    Paragraph(Text(
                        "The literal P is the subtype of T times E with f(t)=a(e), with the induced product topology. "
                        + "The standard projections are continuous and both onto: P to E uses the left representative of a(e), "
                        + "whereas P to T uses surjectivity of a at f(t). The common composite rho equals both p after the T projection "
                        + "and the first coordinate of a after the E projection.")),
                    Paragraph(Text(
                        "Separate the entire closed fibers A0=a inverse{(star,0)} and A1=a inverse{(star,1)} by a clopen H, "
                        + "using compact Hausdorff zero-dimensional separation. K=a(H) is closed, contains the lower endpoint and excludes the upper endpoint. "
                        + "Apply the section construction. Fs={e:a(e)=((a(e)).first,s((a(e)).first))} is a closed equalizer. "
                        + "The explicit map E disjoint-sum Fs to P sends e to (inl(a(e)),e) and an Fs point to (inr((a(e)).first),e). "
                        + "It is continuous and bijective, hence a homeomorphism by compactness and Hausdorffness. This proves compactness and "
                        + "zero-dimensionality of P, with no metrizability assumption on E.")),
                    Paragraph(Text(
                        "The clopen subset G of P consists of points whose E coordinate lies in H and whose T coordinate lies in the right summand. "
                        + "Although Fs need not be open in E, the right summand is clopen in the pullback, and H restricts to a clopen in Fs. "
                        + "The image rho(G) equals D exactly, using one common compatible E witness in each direction. Consequently rho is not open. "
                        + "For every type Y in an independent universe, every topology on Y and every continuous onto h:Y to P, rho after h is not open. "
                        + "This last clause directly applies upstream IsOpenMap.of_comp; no extra compactness or openness of h is assumed.")),
                    Paragraph(Text(
                        "The quantifiers are for every already selected a there exists a later f. They do not exchange to one fixed p defeating all adaptive resolutions. "
                        + "The certificate also retains the actual pullback homeomorphism, so no proper subset or replacement relation is called the full pullback. "
                        + "This is not a counterexample to Res(B), a resolution of Peng Question 5.1, or a global novelty or unique-result claim. "
                        + "The relative metric-kernel supplier remains applicable to the constructed metrizable T. "
                        + "The construction is recorded in Library/Topology/project2026openpullbackobstruction.md. Context is in Library/Topology/project2026relativeopenresolution.md and Library/Topology/valov2008milyutinmaps.md; "
                        + "the self-contained obstruction is a project derivation, without attributing it to uninspected primary-source bodies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("preselection-stability-refuted"),
                DeclarationHandle.Create(Owner + "result"),
                H("Universal preselection stability is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, V("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "claim is literally a closed Prop. It asks for one compact Hausdorff zero-dimensional E and continuous onto a:E to Square, "
                    + "initially open over Cantor, whose full pullback remains open over Cantor for every compact metrizable later extension f. "
                    + "Those extensions must be continuous and onto, open and onto over Cantor, have forgetting fibers of size at most two, "
                    + "and admit a continuous Bool label making (f,label) a closed embedding. result has the literal type Not claim. "
                    + "The proof applies exists_obstruction to the alleged preselection and uses its actual binary extension; "
                    + "it assumes neither a missing construction nor a nonopen incidence set."))),
                DescribeRole.Theorem))));
}
