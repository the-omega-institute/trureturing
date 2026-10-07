using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Hunter;
internal sealed class NCHunterKernelRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Analytic/Hunter/NCHunterKernelRigidity.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/Analytic/garciavolcic2025hunter");
    public DocumentDefinition Create()
    {
        Formula n=F.Id("n"),d=F.Id("d"),h=F.Id("H"),x=F.Id("X"),i=F.Id("i");
        Formula sourceX1=Seq(F.Id("X"),Underscore,Grp(D(1)));
        Formula sourceXn=Seq(F.Id("X"),Underscore,Grp(n));
        Formula sourceH=Seq(F.Id("H"),Underscore,Grp(Seq(D(2),d)));
        Formula sourceMu=Seq(Mu,Underscore,Grp(n,Comma,d));
        Formula ker=Call("LinearMap.ker",Call("ContinuousLinearMap.toLinearMap",Call("residual",n,d,x)));
        Formula commonKernel=Seq(Seq(Operatorname,Grp(F.Id("iInf"))),Underscore,Grp(i,Colon,Fin(n)),Sp,
            Call("LinearMap.ker",Call("ContinuousLinearMap.toLinearMap",At(x,i))));
        Formula body=Nd(Imp(LeTo(D(2),n),Imp(LeTo(D(2),d),Hilbert(h,All(x,Arrow(Fin(n),Operators(h)),
            Imp(SelfAdjoints(x,n),Eqn(ker,commonKernel)))))));
        Formula claim=new Formula.Logic(F.Id("claim"),FormulaLogicOperator.Iff,Parenthesized(body));
        return DocumentDefinition.Create(ScribeNode.Create(
            "For every bounded self-adjoint tuple on a complex Hilbert space, the sharp Hunter residual has exactly the common kernel of the tuple.",
            H("Garcia--Volcic kernel rigidity"),Blocks(
                Describe.Lean(DescribeId.Create("nc-hunter-kernel-claim"),DeclarationHandle.Create(Prefix+"claim"),
                    H("Conjecture 4.5"),StatementSource.FromAuthor(Disp(claim)),AssessedProvenance.FromLiterature(Source),
                    Blocks(Paragraph(Text("Conjecture 4.5, page 11: “Let "), Math(Seq(n,Comma,d,Geq,D(2))),
                        Text(". For all tuples of hermitian operators "), Math(sourceX1), Text(",…,"), Math(sourceXn),
                        Text(" on a Hilbert space, ker ("), Math(sourceH), Text("("), Math(sourceX1), Text(",…,"), Math(sourceXn),
                        Text(") − "), Math(sourceMu), Text("("), Math(new Formula.Power(sourceX1,Seq(D(2),d))), Text(" + ⋯ + "),
                        Math(new Formula.Power(sourceXn,Seq(D(2),d))), Text(")) = ker "), Math(sourceX1), Text(" ∩ ⋯ ∩ ker "), Math(sourceXn),
                        Text(".” Fin n indexes all n letters starting at zero. H is complete over C; ContinuousLinearMap represents bounded complex-linear operators. LinearMap.ker and iInf are the literal kernels and their intersection. H_{2d} is nchs n (2*d), using the reciprocal-fibre coefficient, and mu retains both parity branches and the n = 1 branch."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("nc-hunter-kernel-result"),DeclarationHandle.Create(Prefix+"result"),
                    H("The kernel equality"),StatementSource.FromAuthor(Disp(F.Id("claim"))),AssessedProvenance.FromRepo(Source),
                    Blocks(Paragraph(Text("The positive residual form forces every mixed-word row to vanish. A strictly positive shifted factorial kernel then forces the grouped word coefficients to vanish. Even and odd degrees use separate contractions. Finally, a self-adjoint operator and its positive powers have the same kernel. The reverse inclusion follows by evaluating every positive-length word on the common kernel."))),DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(ProblemSlugRef.Create("garcia-volcic-2025-nc-hunter-kernel-rigidity"), ResolutionKind.Proved))
            ),[]));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(part == "piCongrLeft'" ? Seq(F.Id("piCongrLeft"), Apos) : F.Id(part));
        }
        return arguments.Length == 0 ? Seq(Operatorname, Grp([.. parts]))
            : new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. arguments]);
    }
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall, Sp, x, Colon, type, Comma, Sp, body);
    private static Formula Instance(string name, Formula[] args, Formula body) => Seq(OpenBracket, Call(name, args), CloseBracket, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula TypeOf() => Call("Type");
    private static Formula N() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula C() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Hilbert(Formula h, Formula body, bool complete = true) => All(h,TypeOf(),
        Instance("NormedAddCommGroup",[h],Instance("InnerProductSpace",[C(),h],
            complete ? Instance("CompleteSpace",[h],body) : body)));
    private static Formula Operators(Formula h) => Call("ContinuousLinearMap",C(),h,h);
    private static Formula SelfAdjoints(Formula x, Formula n) => All(F.Id("i"),Fin(n),Call("IsSelfAdjoint",At(x,F.Id("i"))));
    private static Formula Nd(Formula body) => All(F.Id("n"),N(),All(F.Id("d"),N(),body));
}
