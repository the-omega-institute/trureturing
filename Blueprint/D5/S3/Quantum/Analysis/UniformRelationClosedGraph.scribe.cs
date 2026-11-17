using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class UniformRelationClosedGraphDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Quantum/Analysis/UniformRelationClosedGraph";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single finite relation formula on all actual outputs recovers the original total relation as a bounded real bilinear map on a Banach space.",
        H("Uniform relation readouts and closed graphs"), Blocks(
            Describe.Lean(DescribeId.Create("actual-output-set"),
                DeclarationHandle.Create(Root+".outputs"), H("Actual outputs"),
                StatementSource.FromAuthor(F.Disp(All("E",Call("RealNormedSpace"),
                    All("D",Call("TotalBinaryMaps",Id("E")),
                        Eq(Call("outputs",Id("D")),Call("range",Call("uncurry",Id("D")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The set is the literal range of D on all pairs of original inputs. No linear span, closure or output realization is included.")))),
            Describe.Lean(DescribeId.Create("one-formula-for-all-outputs"),
                DeclarationHandle.Create(Root+".UniformReadout"), H("Uniform finite readout"),
                StatementSource.FromAuthor(F.Disp(ReadoutDefinition())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For each original continuous evaluation alpha and positive eta choose a natural number m, tests t indexed by Fin(m), evaluations beta indexed by Fin(m), and real coefficients c indexed by Fin(m). Each test is an actual output and each beta belongs to the same original family P. The displayed bound then holds for every actual output p with those same choices. The index may be empty, and tests and evaluations may repeat. No coefficient bound is imposed.")))),
            Describe.Lean(DescribeId.Create("same-total-relation-bounded-bilinear"),
                DeclarationHandle.Create(Root+".bilinear_bounded"), H("Recovery in the original Banach norm"),
                StatementSource.FromAuthor(F.Disp(Recovery())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("E is any real Banach space in any universe, including the zero space. P is any subset of its continuous real dual that separates points; zero evaluations are allowed. S is a continuous real bilinear map represented by E to continuous linear maps from E to E, and is symmetric. D initially is only a total map on the same E. Conjugacy uses the actual complex numbers alpha(S(a,b))-i alpha(D(a,b)), for every original alpha and both original inputs. The rebracketing identity is required on every original triple, including nested outputs. No regularity, additivity, homogeneity, measurability or boundedness of D is a hypothesis.")),
                    Paragraph(Text("Conjugacy and separation give skewness. Applying the real rebracketing law to its three cyclic permutations and eliminating the three nested terms gives D(D(a,b),t)=S(b,S(a,t))-S(a,S(b,t)). This argument never expands D on a sum. A common finite readout formula reflects every finite real dependency among actual output rows back to the outputs. Apply that reflection to the three outputs D(a+b,c), D(a,c), D(b,c), and then to the two outputs D(r a,b), D(a,b). This proves real linearity in the first slot; skewness supplies the second slot.")),
                    Paragraph(Text("For a fixed a take b(n) tending to x and D(a,b(n)) tending to y. Fix alpha and eta and choose one readout formula. It applies to all actual outputs D(a,b(n)) and to D(a,x), without requiring y to be an output. The nested identity expresses each finite readout as a continuous function of b(n), using only S and the original continuous evaluations. Passing to the limit yields an error at most eta times the norm of y. Comparing with the formula at D(a,x) bounds the difference of their alpha values by eta times the sum of their norms. Let eta tend to zero and use separation. Thus each original linear row has a closed graph.")),
                    Paragraph(Text("The Banach closed-graph theorem makes each row continuous. Skewness bounds the rows indexed by the original closed unit ball pointwise, using the opposite row. Banach-Steinhaus gives a common operator bound. Scaling gives the displayed finite joint bound and the continuous bilinear map B, whose value equals D on every original pair. Closed graph and Banach-Steinhaus are the pinned Mathlib suppliers; no new relation is selected.")),
                    Paragraph(Text("For an Archimedean order-unit application, use its original norm and original separating positive continuous evaluations. Positivity, cone and unit are unnecessary for this implication, so the theorem applies without changing them. It assumes neither complex positive tables nor a Jordan identity, finite dimension, a predual or a representation. It supplies no extension from an incomplete original domain, Leibniz law, cone preserving flow, physical preparation or instrument. The finite-dependency algebra is the dimension independent subargument of the three-label theory; the analytical bridge uses the uniform formula on actual outputs. No literature priority is asserted."))),
                DescribeRole.Theorem))));

    private static Formula ReadoutDefinition()
    {
        var E=Id("E"); var P=Id("P"); var D=Id("D"); var eta=Id("eta");
        var p=Id("p"); var j=Id("j"); var t=Id("t"); var beta=Id("beta"); var c=Id("c");
        var A=Call("outputs",D); var m=Id("m"); var alpha=Id("alpha");
        var sum=Seq(new Formula.Subscript(F.Sum, Seq(j,F.InMacro,Sp,Call("Fin",m))),Sp,
            Mul(At(c,j),At(At(beta,j),At(D,p,At(t,j)))));
        var law=All("alpha",P,All("eta",Call("PositiveReals"),
            Exists("m",Call("Naturals"),Exists("t",Call("Functions",Call("Fin",m),A),
            Exists("beta",Call("Functions",Call("Fin",m),P),
            Exists("c",Call("Functions",Call("Fin",m),Call("Reals")),
            All("p",A,Le(Call("abs",Sub(At(alpha,p),sum)),Mul(eta,Norm(p))))))))));
        return All("E",Call("RealNormedSpace"),All("P",Call("Subsets",Call("ContinuousDual",E)),
            All("D",Call("TotalBinaryMaps",E),Iff(Call("UniformReadout",P,D),law))));
    }

    private static Formula Recovery()
    {
        var E=Id("E"); var P=Id("P"); var S=Id("S"); var D=Id("D");
        var a=Id("a"); var b=Id("b"); var c=Id("c"); var alpha=Id("alpha");
        Formula G(Formula x,Formula y)=>Sub(Call("complex",At(alpha,At(S,x,y))),
            Mul(Id("i"),Call("complex",At(alpha,At(D,x,y)))));
        var separation=All("x",E,Implies(All("alpha",P,Eq(At(alpha,Id("x")),F.D(0))),Eq(Id("x"),F.D(0))));
        var symmetry=All("a",E,All("b",E,Eq(At(S,a,b),At(S,b,a))));
        var conjugacy=All("alpha",P,All("a",E,All("b",E,Eq(G(b,a),Call("conj",G(a,b))))));
        var rebracketing=All("a",E,All("b",E,All("c",E,
            Eq(Sub(At(S,At(S,a,b),c),At(S,a,At(S,b,c))),
                Sub(At(D,At(D,a,b),c),At(D,a,At(D,b,c)))))));
        var conclusion=Exists("B",Call("ContinuousRealBilinearMaps",E,E,E),
            And(All("a",E,All("b",E,Eq(At(Id("B"),a,b),At(D,a,b)))),
                Exists("K",Call("Reals"),And(Le(F.D(0),Id("K")),
                    All("a",E,All("b",E,Le(Norm(At(D,a,b)),Mul(Mul(Id("K"),Norm(a)),Norm(b)))))))));
        return All("E",Call("RealBanachSpace"),All("P",Call("Subsets",Call("ContinuousDual",E)),
            All("S",Call("ContinuousRealBilinearMaps",E,E,E),All("D",Call("TotalBinaryMaps",E),
                Implies(And(separation,symmetry,conjugacy,rebracketing,Call("UniformReadout",P,D)),conclusion)))));
    }
    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] a)=>new Formula.Apply(Id(s),[..a]);
    private static Formula At(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Exists(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Norm(Formula a)=>new Formula.Norm(a);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] a)
    {var r=a[^1];for(var i=a.Length-2;i>=0;i--)r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);return r;}
}
