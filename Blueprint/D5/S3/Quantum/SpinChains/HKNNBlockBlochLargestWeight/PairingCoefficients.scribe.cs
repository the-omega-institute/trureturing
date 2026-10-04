using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;
internal sealed class HKNNPairingCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/liwu2026j1j2rings");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed pairing coefficients and cyclic translation", H("Signed pairing coefficients and cyclic translation"), Blocks(
            Node("s", "Li and Wu, p. 3, after Eq. (4): \"[i, j] ≡ | ↑⟩i | ↓⟩j − | ↓⟩i | ↑⟩j is a singlet state on sites i and j.\". The two nonzero integer coefficients are +1 and -1.", sFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("term", "Each unordered edge contributes once, with its smaller endpoint first. The product is the computational-basis coefficient of its tensor product of singlets.", termFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("psi", "Li and Wu, p. 4, Eq. (6): \"|ψHKNN⟩ = Σ_{aj<bj and a1<a2<···<aN/2} [a1, b1] · · · [aN/2, bN/2], (6)\"; \"where the sum is over all partitions of {1, 2, . . . , N} into pairs without regard to order.\" The existing fixed-point-free involution carrier represents each partition once, with no Pfaffian permutation sign.", psiFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("block", "The first m sites are down and the other m sites are up. This is the configuration with all successive down-spin separations equal to one.", blockFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("balanced", "A configuration is balanced when exactly m sites are down.", balancedFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("crossing", "Every pair has opposite spins.", crossingFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("Down", "The subtype of down sites retains its site index.", DownFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("Up", "The complementary subtype of up sites retains its site index.", UpFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("CrossPairings", "Crossing pairings are precisely the opposite-spin pair partitions.", CrossPairingsFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("K", "K is the number of crossing pair partitions for the block configuration. Its positivity and the equality of balanced-sector counts follow from explicit equivalences.", KFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("shift", "The translation acts on coefficients by the predecessor site modulo 2m. NatMod is natural-number remainder; subtraction on naturals is truncated. Li and Wu define translation by T S_j^- T^{-1} = S_{j+1}^- (p. 2).", shiftFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isArc", "An arc is any cyclic translate of the block configuration.", isArcFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pairing_data", "Crossing involutions give a bijection between down and up sites. The block has one sign on every supported term and K is positive. Transporting down-to-up bijections gives a uniform count. Prescribing two interleaving edges and swapping their partners yields opposite signs and a strict coefficient deficit. Under rotation exactly one pair crosses the cyclic cut, giving a global minus sign. The last two clauses state the site formula for iterated translation.", pairingdataFormula(), DescribeRole.Theorem, AssessedProvenance.FromRepo())
        ), []));
    private static DocumentBlock Node(string name, string prose, Formula formula, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hknn-pairingcoefficients-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Exists(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
    private static Formula Negate(Formula x) => Seq(Neg, Sp, Parenthesized(x));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Rvert);
    private static Formula Lambda(string v, Formula type, Formula body) => Seq(F.Id(v), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Subtype(string v, Formula type, Formula body) => Seq(OpenBrace, F.Id(v), Colon, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula BigSum(string v, Formula type, Formula body) => Seq(Sum, Underscore, Grp(Seq(F.Id(v), Colon, type)), Sp, body);
    private static Formula BigProd(string v, Formula type, Formula body) => Seq(Prod, Underscore, Grp(Seq(F.Id(v), InMacro, Sp, type)), Sp, body);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula B() => Named("Bool");
    private static Formula Sites(Formula m) => Call("Fin", Mul(D(2), m));
    private static Formula Config(Formula m) => Call("Stationing", Mul(D(2), m));
    private static Formula Pairings(Formula m) => Call("FixedPointFreeInvolution", Sites(m));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Iterate(Formula m, Formula j, Formula x) => Call("iterate", Call("shift",m), j, x);
    private static Formula Conjunction(params Formula[] items) => items.Reverse().Aggregate((x,y) => And(y,x));
    private static Formula WithInstance(Formula m, Formula body) => Seq(OpenBracket,Call("NeZero",Mul(D(2),m)),CloseBracket,Sp,body);
    private static Formula PairingDataBody()
    {
        Formula m=F.Id("m"), x=F.Id("x"), f=F.Id("f"), d=F.Id("d"), e=F.Id("e"), u=F.Id("u"), v=F.Id("v"), j=F.Id("j"), i=F.Id("i");
        Formula support=All("x",Config(m),All("f",Pairings(m),Imp(Call("crossing",x,f),Call("balanced",m,x))));
        Formula bounds=And(Lt(D(0),Call("K",m)),And(Eq(Abs(Call("psi",m,Call("block",m))),Call("castInt",Call("K",m))),
            And(All("x",Config(m),Imp(Negate(Call("balanced",m,x)),Eq(Call("psi",m,x),D(0)))),
                All("x",Config(m),Le(Abs(Call("psi",m,x)),Call("castInt",Call("K",m)))))));
        Formula interleave=All("x",Config(m),Imp(Call("balanced",m,x),All("d",Call("Down",m,x),All("e",Call("Down",m,x),
            All("u",Call("Up",m,x),All("v",Call("Up",m,x),Imp(Lt(Val(d),Val(u)),Imp(Lt(Val(u),Val(e)),
                Imp(Lt(Val(e),Val(v)),Lt(Abs(Call("psi",m,x)),Call("castInt",Call("K",m))))))))))));
        Formula rotation=WithInstance(m,Imp(Le(D(1),m),All("x",Config(m),Eq(Call("psi",m,Call("shift",m,x)),new Formula.Negate(Call("psi",m,x))))));
        Formula index=Call("FinIndex",Call("NatMod",Add(Val(i),Mul(Sub(Mul(D(2),m),D(1)),j)),Mul(D(2),m)),Sites(m));
        Formula coordinate=All("x",Config(m),All("j",N(),All("i",Sites(m),Eq(Call("apply",Iterate(m,j,x),i),Call("apply",x,index)))));
        Formula subtraction=WithInstance(m,Imp(Le(D(1),m),All("x",Config(m),All("j",N(),All("i",Sites(m),
            Eq(Call("apply",Iterate(m,j,x),i),Call("apply",x,Sub(i,Call("castFin",j,Sites(m))))))))));
        return All("m",N(),Conjunction(support,bounds,interleave,rotation,coordinate,subtraction));
    }
    private static Formula sFormula()
    {
        Formula a=F.Id("a"), b=F.Id("b");
        return Eq(Named("s"),Lambda("a",B(),Lambda("b",B(),Call("ite",And(Eq(a,Named("false")),Eq(b,Named("true"))),D(1),Call("ite",And(Eq(a,Named("true")),Eq(b,Named("false"))),new Formula.Negate(D(1)),D(0))))));
    }
    private static Formula termFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), i=F.Id("i"), f=F.Id("f");
        return All("m",N(),All("x",Config(m),All("f",Pairings(m),Eq(Call("term",m,x,f),BigProd("i",Call("filter",Call("univ",Sites(m)),Lambda("i",Sites(m),Lt(i,Call("apply",Val(f),i)))),Call("s",Call("apply",x,i),Call("apply",x,Call("apply",Val(f),i))))))));
    }
    private static Formula psiFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), f=F.Id("f");
        return All("m",N(),All("x",Config(m),Eq(Call("psi",m,x),BigSum("f",Pairings(m),Call("term",m,x,f)))));
    }
    private static Formula blockFormula()
    {
        Formula m=F.Id("m"), i=F.Id("i");
        return All("m",N(),Eq(Call("block",m),Lambda("i",Sites(m),Call("decide",Lt(Val(i),m)))));
    }
    private static Formula balancedFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), i=F.Id("i");
        return All("m",N(),All("x",Config(m),Eq(Call("balanced",m,x),Eq(Call("card",Call("filter",Call("univ",Sites(m)),Lambda("i",Sites(m),Eq(Call("apply",x,i),Named("true"))))),m))));
    }
    private static Formula crossingFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), i=F.Id("i"), f=F.Id("f");
        return All("m",N(),All("x",Config(m),All("f",Pairings(m),Eq(Call("crossing",x,f),All("i",Sites(m),Ne(Call("apply",x,i),Call("apply",x,Call("apply",Val(f),i))))))));
    }
    private static Formula DownFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), i=F.Id("i");
        return All("m",N(),All("x",Config(m),Eq(Call("Down",m,x),Subtype("i",Sites(m),Eq(Call("apply",x,i),Named("true"))))));
    }
    private static Formula UpFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), i=F.Id("i");
        return All("m",N(),All("x",Config(m),Eq(Call("Up",m,x),Subtype("i",Sites(m),Ne(Call("apply",x,i),Named("true"))))));
    }
    private static Formula CrossPairingsFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), f=F.Id("f");
        return All("m",N(),All("x",Config(m),Eq(Call("CrossPairings",m,x),Subtype("f",Pairings(m),Call("crossing",x,f)))));
    }
    private static Formula KFormula()
    {
        Formula m=F.Id("m");
        return All("m",N(),Eq(Call("K",m),Call("card",Call("CrossPairings",m,Call("block",m)))));
    }
    private static Formula shiftFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), i=F.Id("i");
        return All("m",N(),All("x",Config(m),Eq(Call("shift",m,x),Lambda("i",Sites(m),Call("apply",x,Call("FinIndex",Call("NatMod",Add(Val(i),Parenthesized(Sub(Mul(D(2),m),D(1)))),Mul(D(2),m)),Sites(m)))))));
    }
    private static Formula isArcFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), j=F.Id("j");
        return All("m",N(),All("x",Config(m),Eq(Call("isArc",m,x),Exists("j",N(),Eq(x,Iterate(m,j,Call("block",m)))))));
    }
    private static Formula pairingdataFormula()
    {
        return PairingDataBody();
    }
}
