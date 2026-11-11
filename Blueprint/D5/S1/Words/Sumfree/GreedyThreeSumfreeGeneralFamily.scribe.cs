using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sumfree;

internal sealed class GreedyThreeSumfreeGeneralFamilyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/vanberkelbosma2026sumfree");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theorem 19 gives the full seeded greedy range and exact characteristic periodicity.",
        H("The general three-seed family"),
        Blocks(
            Paragraph(Text("Theorem 19 establishes the eventual difference pattern for this family. "
                + "The interval formula below expresses the same sequence as a set of integers. "
                + "The least characteristic period and its earliest integer onset follow directly "
                + "from that formula. A characteristic preperiod counts positive integer positions; "
                + "the source's f+g+2 preperiod counts sequence entries and differences.")),
            Paragraph(Text("All number variables are natural. Write a=f+g, h=g+d, "
                + "b=f+2g+d-1 and M=3f+5g+2d-3=3a+2h-3. Subtractions in the formulas "
                + "are natural subtractions. Icc denotes a closed interval, mod denotes remainder, "
                + "and a set used as a predicate denotes membership. The admitted domain is "
                + "1 <= f < g, d >= 2, f+g >= d+1, excluding only (1,2,2).")),
            Node("A", "The initial and periodic blocks", CandidateFormula(),
                "The two isolated seeds precede I(0)=[h,b]. For every positive j, "
                + "I(j)=jM+[h-2,b-2]. Each interval has f+g entries; the first omission "
                + "block is two integers shorter than every subsequent omission block.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("greedyPrefix", "The literal greedy recurrence", PrefixFormula(),
                "The list is stored in decreasing order. Starting from [h,g,f], each step "
                + "prepends the least integer larger than the head that is not the sum of "
                + "three distinct list entries. The distinctness condition is x<y<w, so "
                + "repeated summands are forbidden. The minimum always exists: an integer "
                + "larger than the head and three times the sum of the list cannot be such a sum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("S", "The greedy sequence's range", RangeFormula(),
                "Membership means occurrence in some literal greedy prefix. No periodic "
                + "membership formula is used in the recurrence defining these prefixes.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("restricted_three_sum_eq_complement", "The exact restricted sum invariant", ComplementFormula(),
                "RestrictedThreeSum(P,n) means that x+y+w=n for x<y<w with all three "
                + "entries in P, using the existing two-parameter definition. Four interval "
                + "sum families cover the initial gap and every later gap uniformly in j. "
                + "Conversely the sum of the three residues lies between b-1 and M+h-3. "
                + "The top two residues b-1 and b occur only in the initial interval. "
                + "Distinct periodic entries may share a residue; the bounds retain these cases. "
                + "The exclusion (1,2,2) is needed at the last initial overlap, and both the "
                + "boundary f+g=d+1 and every other d=2 case are included.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("s_eq_A", "The actual greedy range equals the block set", EqualityFormula(),
                "The prefix invariant states that every candidate up to the current head "
                + "occurs in the prefix. The least-next-entry rule excludes any candidate "
                + "between consecutive heads by the sum invariant. If the next head were "
                + "not a candidate, that invariant would supply a forbidden triple of earlier "
                + "entries. The heads grow at least by one at each step, proving the full range equality.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("PeriodFrom", "Characteristic periodicity from an integer position", PeriodFormula(),
                "PeriodFrom(P,q,N) compares membership at n and n+q for every n >= N. "
                + "It refers to integer positions, independently of the enumeration of P.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("characteristic_periods", "All eventual periods and their earliest onset", ExactPeriodsFormula(),
                "For n>b, membership is exactly h-2 <= n mod M <= b-2. This cyclic "
                + "interval has a unique transition from zero to one. A shift preserving "
                + "it fixes that transition, forcing divisibility by M. Moreover b belongs "
                + "to the sequence, whereas b+q is absent for every positive multiple q "
                + "of M. Thus the least positive eventual characteristic period is M, "
                + "the least characteristic preperiod length is b, and the first periodic "
                + "integer is b+1. This is a direct deduction from the range formula. "
                + "For Example 20, (f,g,d)=(3,7,6), the blocks are [13,22], [64,73], "
                + "[117,126], and so on; M=53 and characteristic periodicity starts at 23.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("greedy-general-" + name.ToLowerInvariant().Replace('_','-')),
        DeclarationHandle.Create("D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily." + name),
        H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula CandidateFormula()
    {
        var t=F.Id("t"); var r=F.Id("r");
        var translate=Par(Seq(r,Sp,Mapsto,Sp,Add(Mul(t,M()),r)));
        var blocks=Seq(new Formula.Subscript(Named("union"),Seq(t,Sp,Ge,Sp,D(1))),Sp,
            Call("image",translate,Call("Icc",L(),U())));
        return Disp(Seq(Params("f","g","d"),Call("A",Ff(),G(),Dd()),Sp,Eq,Sp,
            Call("union",Call("union",new Formula.SetLiteral([Ff(),G()]),Call("Icc",Hh(),B())),blocks),Dot));
    }
    private static Formula PrefixFormula()
    {
        var n=F.Id("n"); var z=F.Id("z"); var p=Call("greedyPrefix",Ff(),G(),Dd(),n);
        var choices=Seq(OpenBrace,z,Sp,InMacro,Sp,Nat(),Sp,Mid,Sp,
            Call("headD",p,D(0)),Sp,Lt,Sp,z,Sp,Land,Sp,Neg,Sp,Par(Triple(z,x=>Member(x,p))),CloseBrace);
        return Disp(Seq(Params("f","g","d"),Call("greedyPrefix",Ff(),G(),Dd(),D(0)),Sp,Eq,Sp,
            Seq(OpenBracket,Hh(),Comma,Sp,G(),Comma,Sp,Ff(),CloseBracket),Sp,Land,Sp,
            Par(Seq(Forall,Sp,n,Colon,Sp,Nat(),Comma,Sp,
                Call("greedyPrefix",Ff(),G(),Dd(),Add(n,D(1))),Sp,Eq,Sp,Call("cons",Seq(Min,Sp,choices),p))),Dot));
    }
    private static Formula RangeFormula() => Disp(Seq(Params("f","g","d","z"),
        Call("S",Ff(),G(),Dd(),F.Id("z")),Sp,Leftrightarrow,Sp,Exists,Sp,F.Id("n"),Colon,Sp,Nat(),Comma,Sp,
        Member(F.Id("z"),Call("greedyPrefix",Ff(),G(),Dd(),F.Id("n"))),Dot));
    private static Formula ComplementFormula() => Disp(Seq(Params("f","g","d","z"),Hyp(),Sp,Implies,Sp,
        Par(Seq(Call("RestrictedThreeSum",Call("A",Ff(),G(),Dd()),F.Id("z")),Sp,Leftrightarrow,Sp,
            Par(Seq(Hh(),Sp,Lt,Sp,F.Id("z"),Sp,Land,Sp,Neg,Sp,Par(Member(F.Id("z"),Call("A",Ff(),G(),Dd()))))))),Dot));
    private static Formula EqualityFormula() => Disp(Seq(Params("f","g","d"),Hyp(),Sp,Implies,Sp,
        Par(Seq(Call("S",Ff(),G(),Dd()),Sp,Eq,Sp,Call("A",Ff(),G(),Dd()))),Dot));
    private static Formula PeriodFormula()
    {
        var p=F.Id("P"); var n=F.Id("n"); var q=F.Id("q"); var nn=F.Id("N");
        return Disp(Seq(Forall,Sp,p,Colon,Sp,Par(Seq(Nat(),Sp,To,Sp,Named("Prop"))),Comma,Sp,
            Params("q","N"),Call("PeriodFrom",p,q,nn),Sp,Leftrightarrow,Sp,
            Par(Seq(Forall,Sp,n,Colon,Sp,Nat(),Comma,Sp,nn,Sp,Le,Sp,n,Sp,Implies,Sp,
                Par(Seq(new Formula.Apply(p,[Add(n,q)]),Sp,Leftrightarrow,Sp,new Formula.Apply(p,[n]))))),Dot));
    }
    private static Formula ExactPeriodsFormula() => Disp(Seq(Params("f","g","d","q","N"),Hyp(),Sp,Implies,Sp,
        D(0),Sp,Lt,Sp,F.Id("q"),Sp,Implies,Sp,
        Par(Seq(Call("PeriodFrom",Call("S",Ff(),G(),Dd()),F.Id("q"),Add(F.Id("N"),D(1))),Sp,Leftrightarrow,Sp,
            Par(Seq(M(),Sp,Mid,Sp,F.Id("q"),Sp,Land,Sp,B(),Sp,Le,Sp,F.Id("N"))))),Dot));
    private static Formula Hyp() => Par(Seq(D(1),Sp,Le,Sp,Ff(),Sp,Land,Sp,Ff(),Sp,Lt,Sp,G(),Sp,Land,Sp,
        D(2),Sp,Le,Sp,Dd(),Sp,Land,Sp,Add(Dd(),D(1)),Sp,Le,Sp,Add(Ff(),G()),Sp,Land,Sp,
        Par(Seq(Ff(),Sp,Neq,Sp,D(1),Sp,Lor,Sp,G(),Sp,Neq,Sp,D(2),Sp,Lor,Sp,Dd(),Sp,Neq,Sp,D(2)))));
    private static Formula Triple(Formula z,Func<Formula,Formula> membership)
    {
        var x=F.Id("x");var y=F.Id("y");var w=F.Id("w");
        return Seq(Exists,Sp,x,Comma,Sp,y,Comma,Sp,w,Colon,Sp,Nat(),Comma,Sp,
            Par(Seq(x,Sp,Lt,Sp,y,Sp,Land,Sp,y,Sp,Lt,Sp,w,Sp,Land,Sp,
                membership(x),Sp,Land,Sp,membership(y),Sp,Land,Sp,membership(w),Sp,Land,Sp,
                Add(Add(x,y),w),Sp,Eq,Sp,z)));
    }
    private static Formula Ff()=>F.Id("f");
    private static Formula G()=>F.Id("g");
    private static Formula Dd()=>F.Id("d");
    private static Formula Hh()=>Add(G(),Dd());
    private static Formula B()=>Sub(Add(Add(Ff(),Mul(D(2),G())),Dd()),D(1));
    private static Formula M()=>Sub(Add(Add(Mul(D(3),Ff()),Mul(D(5),G())),Mul(D(2),Dd())),D(3));
    private static Formula L()=>Sub(Hh(),D(2));
    private static Formula U()=>Sub(B(),D(2));
    private static Formula Nat()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Named(string name)=>Seq(Operatorname,Grp(F.Id(name)));
    private static Formula Call(string name,params Formula[] args)=>new Formula.Apply(Named(name),[..args]);
    private static Formula Par(Formula x)=>Seq(Open,x,Close);
    private static Formula Member(Formula x,Formula set)=>Seq(x,Sp,InMacro,Sp,set);
    private static Formula Params(params string[] names)
    {
        var xs=new List<Formula>();
        foreach(var name in names){if(xs.Count>0)xs.AddRange([Comma,Sp]);xs.Add(F.Id(name));}
        return Seq(Forall,Sp,Seq([..xs]),Colon,Sp,Nat(),Comma,Sp);
    }
    private static Formula Add(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
}
