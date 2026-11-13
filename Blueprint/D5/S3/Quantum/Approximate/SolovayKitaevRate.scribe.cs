using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate.SolovayKitaevRateNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class SolovayKitaevRateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Approximate/SolovayKitaevRate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar three-halves error recurrence and fivefold length growth yield the exact logarithmic exponent log(5)/log(3/2).",
        H("Solovay–Kitaev error and level estimates"),Blocks(
            Paragraph(Text("These scalar and logarithmic proofs are Apache-2.0 reuse from Zayn Blore's CSD SolovayKitaevStep and SolovayKitaevCount at commit 9b2d2c17e926ae13795119c5f2f62e85ea240c2d. Their exact original file and declaration references appear in the Lean source. The full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. They bound scalar sequences and level counts; the ordinary-word theorem separately supplies one actual list satisfying error and length together.")),
            Entry("scalar-error-closure","skError_le_rpow","Closed scalar error bound",ErrorClosure(),
                "For a nonnegative error sequence with e(n+1)<=C*e(n)^(3/2), induction gives double exponential decay after multiplication by C^2. C is any positive real constant."),
            Entry("step-estimate","step_bound","The sufficient three-halves step",StepBound(),
                "At a=sqrt(2)*sqrt(epsilon)+epsilon and delta=epsilon, the commutator stability expression is at most 33*epsilon^(3/2) whenever sqrt(epsilon)<=1/2."),
            Entry("level-reaches-error","skLevel_rpow_le","The chosen level reaches the error",LevelError(),
                "For 0<epsilon<=b<1, skLevel(b,epsilon)=ceil(log(log(epsilon)/log(b))/log(3/2)). At this level the closed error is at most epsilon."),
            Entry("level-fivefold-cost","five_pow_skLevel_le","Fivefold growth is polylogarithmic",LevelLength(),
                "Rounding the level upward costs a factor of at most five. The exponent is exactly log(5)/log(3/2); this scalar estimate asserts no word-length bound without a paired word construction."))));
    private static DocumentBlock.Describe Entry(string id,string name,string title,Formula formula,string body) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(formula),AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/dawsonnielsen2006solovaykitaev")),
            Blocks(Paragraph(Text(body))),DescribeRole.Theorem);
    private static Formula ErrorClosure()
    {
        Formula c=X("C"),e=X("e"),n=X("n"),j=X("j");
        Formula nonneg=All("j",Call("Nat"),Le(N(0),At(e,j)));
        Formula rec=All("j",Call("Nat"),Le(At(e,Add(j,N(1))),Multiply(c,Pow(At(e,j),Frac(N(3),N(2))))));
        Formula result=All("n",Call("Nat"),Le(Multiply(Pow(c,N(2)),At(e,n)),
            Pow(Multiply(Pow(c,N(2)),At(e,N(0))),Pow(Frac(N(3),N(2)),n))));
        return All("C",Call("Real"),All("e",new Formula.TypeArrow(Call("Nat"),Call("Real")),
            Imp(And(Pos(c),And(nonneg,rec)),result)));
    }
    private static Formula StepBound()
    {
        Formula e=X("epsilon"),a=Add(Multiply(Call("sqrt",N(2)),Call("sqrt",e)),e);
        Formula result=Le(Multiply(Multiply(Multiply(N(4),a),e),Add(N(1),a)),Multiply(N(33),Pow(e,Frac(N(3),N(2)))));
        return All("epsilon",Call("Real"),Imp(And(Le(N(0),e),Le(Call("sqrt",e),Frac(N(1),N(2)))),result));
    }
    private static Formula Level(Formula body) => All("b",Call("Real"),All("epsilon",Call("Real"),
        Imp(And(Pos(X("b")),And(Lt(X("b"),N(1)),And(Pos(X("epsilon")),Le(X("epsilon"),X("b"))))),body)));
    private static Formula LevelError() => Level(Le(Pow(X("b"),Pow(Frac(N(3),N(2)),
        Call("skLevel",X("b"),X("epsilon")))),X("epsilon")));
    private static Formula LevelLength() => Level(Le(Pow(N(5),Call("skLevel",X("b"),X("epsilon"))),
        Multiply(N(5),Pow(Frac(Call("log",X("epsilon")),Call("log",X("b"))),Exponent()))));
}

internal static class SolovayKitaevRateNotation
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(long n) => new Formula.Number(n);
    internal static Formula All(string n, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    internal static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    internal static Formula At(Formula f, Formula x) => new Formula.Apply(f,[x]);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    internal static Formula Pos(Formula a) => Lt(N(0),a);
    internal static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    internal static Formula Norm(Formula a) => new Formula.Norm(a);
    internal static Formula Star(Formula a) => Call("star",a);
    internal static Formula Words(Formula m) => Call("List",Call("Fin",m));
    internal static Formula Su(Formula a) => And(Unitary(a),Eq(Call("det",a),N(1)));
    internal static Formula Unitary(Formula a) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,Call("unitary",Call("Mat")));
    internal static Formula Member(Formula a, Formula f) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,f);
    internal static Formula Eval(Formula g, Formula w) => Call("evalGamma",g,w);
    internal static Formula Inv(Formula s, Formula w) => Call("inverseWord",s,w);
    internal static Formula Error(Formula g, Formula u, Formula w) => Norm(Subtract(u,Eval(g,w)));
    internal static Formula Comm(Formula v, Formula w) => Multiply(Multiply(Multiply(v,w),Star(v)),Star(w));
    internal static Formula Exponent() => Frac(Call("log",N(5)),Call("log",Frac(N(3),N(2))));
    internal static Formula Alphabet(Formula body) => All("m",Call("Nat"),All("Gamma",
        new Formula.TypeArrow(Call("Fin",X("m")),Call("Mat")),body));
    internal static Formula Generators(Formula m, Formula g) => All("i",Call("Fin",m),Su(At(g,X("i"))));
    internal static Formula ChosenInverse(Formula m, Formula g, Formula s) => All("i",Call("Fin",m),
        Eq(At(g,At(s,X("i"))),Star(At(g,X("i")))));
    internal static Formula Density(Formula m, Formula g) => All("A",Call("Mat"),Imp(Su(X("A")),
        All("eta",Call("Real"),Imp(Pos(X("eta")),Ex("v",Words(m),Lt(Error(g,X("A"),X("v")),X("eta")))))));
    internal static Formula EventStatement()
    {
        Formula m=X("m"),g=X("Gamma"),k=X("K"),b=X("b"),e=X("epsilon"),u=X("U"),w=X("w");
        Formula inverse=All("i",Call("Fin",m),Ex("j",Call("Fin",m),
            Eq(At(g,X("j")),Star(At(g,X("i"))))));
        Formula paired=Ex("w",Words(m),And(Le(Error(g,u,w),e),
            Le(Call("real",Call("length",w)),Multiply(k,Pow(Call("log",Frac(N(1),e)),Exponent())))));
        Formula result=Ex("K",Call("Real"),Ex("b",Call("Real"),And(Pos(k),And(Pos(b),And(Lt(b,N(1)),
            All("epsilon",Call("Real"),Imp(And(Pos(e),Le(e,b)),All("U",Call("Mat"),Imp(Su(u),paired)))))))));
        return Alphabet(Imp(And(Generators(m,g),And(inverse,Density(m,g))),result));
    }
}
