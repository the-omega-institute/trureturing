using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class CZXParentLindbladianWindowChannelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/liuetal2026parentlindbladians");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The CZX parent-Lindbladian window channel and its gauge calculus.",
        H("CZX parent-Lindbladian window channel"),
        Blocks(
            Node("czxU", "The two-site change of basis", CzxU(),
                "The 4 by 4 permutation matrix is the two-site change of basis displayed in Appendix F, with the computational basis in source order (main.tex l. 4858–4863).", Literature),
            Node("czxV", "The signed four-site permutation", CzxV(),
                "The 16 by 16 signed permutation has the fourteen positive entries and two negative entries listed in Appendix F (main.tex l. 4933–4937). Its row and column indices are the four-bit window words.", Literature),
            Node("mu", "The two-site block weight", MuFormula(),
                "The common block weight is the positive real number square root of three divided by four (main.tex l. 4870).", Literature),
            Node("nu", "The four-site block weight", NuFormula(),
                "The multiplicity block weight is square root of three divided by sixteen (main.tex l. 4930).", Literature),
            Node("renormS", "The four-to-two renormalization channel", RenormS(),
                "RenormS conjugates by the signed permutation and the two-site basis change, pinches equal sector labels, and sums the four-dimensional multiplicity index, matching the source's S channel (main.tex l. 3149–3164). Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.", Literature),
            Node("renormT", "The two-to-four renormalization channel", RenormT(),
                "RenormT conjugates by the signed permutation, inserts the normalized multiplicity identity with scalar nu divided by mu, and restores the source tensor order, matching the source's T channel (main.tex l. 3132–3147). The source multiplicity trace satisfies m_lambda = mu_lambda, so the common weight mu is used directly. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.", Literature),
            Node("localChannel", "The four-site channel", LocalChannel(),
                "The local channel applies the four-to-two channel S, then the two-to-four channel T, as in the source's E = T composed with S (main.tex l. 4951–4952).", Literature),
            Node("site", "Cyclic site displacement", Site(),
                "Site i k is the cyclic displacement of i by the natural offset k. The result is represented by the residue modulo n. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.", Literature),
            Node("windowCode", "The four-bit window code", WindowCode(),
                "WindowCode reads four consecutive cyclic bits, with the first site as the most significant bit, and packs them into Fin 16. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.", Literature),
            Node("windowUpdate", "Writing a window word", WindowUpdate(),
                "WindowUpdate replaces the four cyclic window coordinates by the four binary digits of p, in most-significant-first order, and leaves all other coordinates unchanged. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.", Literature),
            Node("windowChannel", "The translated local channel", WindowChannel(),
                "WindowChannel inserts the four-site local channel into a cyclic n-site matrix by summing over the input and output window words and updating the two matrix indices accordingly.", Literature),
            Node("windowSuperoperator", "The matrix of a window channel", WindowSuperoperator(),
                "WindowSuperoperator is the matrix-unit representation of a translated window channel on pairs of binary configurations.", Literature),
            Node("parentLindbladian", "The parent Lindbladian", ParentLindbladian(),
                "The parent Lindbladian is the sum of the translated channel minus the identity over zero-based even starting sites, corresponding to the source's odd-window sum after reindexing (main.tex l. 4951–4952). Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.", Literature),
            Node("tensorX", "The tensor product of bit flips", TensorX(),
                "TensorX has one at the entry taking y to the configuration obtained by adding one in Fin 2 at every site, and zero elsewhere.", Literature),
            Node("cz", "The ring controlled-Z operator", Cz(),
                "Cz is diagonal, with phase minus one raised to the number of adjacent pairs of occupied bits around the cyclic ring.", Literature),
            Node("czxUnitary", "The CZX unitary", CzxUnitary(),
                "The CZX unitary is the controlled-Z operator followed by the tensor product of bit flips, in the source order.", Literature),
            Node("evolution", "Evolution under the parent generator", Evolution(),
                "Evolution applies the matrix exponential of t times the parent Lindbladian to the vector of matrix entries and evaluates it at a pair of configurations.", Literature),
            Node("gauge", "The constant-sector gauge phase", Gauge(),
                "Gauge assigns to a bit e and configuration x the phase minus one raised to e times the cyclic nearest-neighbour occupation sum.", Repo),
            Node("site_injective", "Distinct sites in a four-site window", SiteInjective(),
                "When n is at least four, the four cyclic positions from a fixed starting site are pairwise distinct. The proof cancels the common cyclic displacement modulo n.", Repo, DescribeRole.Theorem),
            Node("windowLM", "The window channel as a linear map", WindowLM(),
                "WindowLM is the complex-linear endomorphism whose action on every matrix is windowChannel.", Repo),
            Node("goodWindow", "A constant gauge window", GoodWindow(),
                "GoodWindow holds when the gauge difference is constant on the four sites of the window.", Repo),
            Node("sectorGauge", "The sector gauge phase", SectorGauge(),
                "SectorGauge is the product phase obtained by weighting every ring edge by the gauge difference at its source site.", Repo),
            Node("gaugedUnit", "A gauged matrix unit", GaugedUnit(),
                "GaugedUnit is the sector phase times the matrix unit from x to x plus delta.", Repo),
            Node("sectorGauge_const", "Constant sectors recover the gauge", SectorGaugeConst(),
                "For a constant difference, distributing the constant over the finite sum identifies sectorGauge with gauge.", Repo, DescribeRole.Theorem),
            Node("sectorGauge_mul_self", "The gauge phase is self-inverse", SectorGaugeMulSelf(),
                "Every sector gauge phase squares to one because its exponent is an integer and the sign square identity applies.", Repo, DescribeRole.Theorem),
            Node("site_succ_injective", "The successor site map is injective", SiteSuccInjective(),
                "The cyclic successor map is injective for every nonempty Fin n. The proof uses the additive inverse in Fin n after establishing n is nonzero from an index.", Repo, DescribeRole.Theorem),
            Node("gauged_window_sector", "The gauged window action", GaugedWindowSector(),
                "On a good window, the gauge converts the local channel into the uniform average over the two middle bits; on a bad window the action is zero. The phase change on the three affected edges cancels using the self-inverse gauge phase.", Repo, DescribeRole.Theorem),
            Node("matrix_linearMap_ext_gauged", "Gauged units span the matrix space", MatrixLinearMapExtGauged(),
                "Two complex-linear endomorphisms agreeing on every gauged unit agree everywhere. Each standard matrix unit is a self-product of a sector phase times one gauged unit, so the standard matrix basis extension applies.", Repo, DescribeRole.Theorem),
            Node("window_channels_commute", "Translated window channels commute", WindowChannelsCommute(),
                "The gauged-unit action identifies each good window channel with an average over its two middle coordinates. The coordinate averages commute, and the four cases of good or bad windows give equality for every matrix.", Repo, DescribeRole.Theorem),
            Node("window_superoperator_action", "The window superoperator action", WindowSuperoperatorAction(),
                "Applying LinearMap.toMatrix_mulVec_repr to windowLM in Matrix.stdBasis identifies the matrix-vector action of windowSuperoperator with windowChannel entrywise.", Repo, DescribeRole.Theorem),
            Node("window_idempotent", "Idempotence of a window superoperator", WindowIdempotent(),
                "The local channel is idempotent on matrix units; the window channel therefore composes with itself to itself. The preceding action formula transfers this identity to the window superoperator.", Repo, DescribeRole.Theorem)
        ), []));

    private static AssessedProvenance Literature => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo => AssessedProvenance.FromRepo(Source);

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("czx-window-" + name.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Local(string name) => Q(Prefix.Replace('/', '.') + name);

    private static Formula Q(string name)
    {
        var parts=name.Split('.'); var items=new List<Formula> { Operatorname, Grp(F.Id(parts[0])) };
        for (var i=1;i<parts.Length;i++) items.AddRange([Dot,Grp(F.Id(parts[i]))]);
        return Seq(items.ToArray());
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula T(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Var(string name) => name == "δ" ? Delta : F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, T(Var(name), type), Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, T(Var(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Const(Formula domain, Formula value) => At(Q("Function.const"), domain, value);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Inv(Formula a) => Pow(a, Neg(D(1)));
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Neg(Formula a) => Seq(Minus, a);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula SumOver(Formula variable, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, domain)), Sp, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinVal(Formula x) => Call("Fin.val", x);
    private static Formula Matrix(Formula r, Formula c, Formula k) => Call("Matrix", r, c, k);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula FinMk(Formula value) => Call("Fin.mk", value);
    private static Formula DivNat(Formula a, Formula b, Formula x) => Call("Fin.divNat", a, b, x);
    private static Formula ModNat(Formula a, Formula b, Formula x) => Call("Fin.modNat", a, b, x);
    private static Formula DivNatFn(Formula a, Formula b) => Call("Fin.divNat", a, b);
    private static Formula ModNatFn(Formula a, Formula b) => Call("Fin.modNat", a, b);
    private static Formula NatDiv(Formula a, Formula b) => Call("Nat.div", a, b);
    private static Formula NatMod(Formula a, Formula b) => Call("Nat.mod", a, b);
    private static Formula CompFin(Formula a, Formula b, Formula x) => Call("Function.comp", a, b, x);
    private static Formula If(Formula c, Formula y, Formula n) => Call("ite", c, y, n);
    private static Formula Cast(Formula x, Formula type) => T(x, type);
    private static Formula COne() => Cast(D(1), Complex());
    private static Formula Matrix16() => Matrix(Fin(D(1,6)), Fin(D(1,6)), Complex());
    private static Formula Matrix4() => Matrix(Fin(D(4)), Fin(D(4)), Complex());
    private static Formula Config(Formula n) => Arrow(Fin(n), Fin(D(2)));
    private static Formula ConfigMatrix(Formula n) => Matrix(Config(n), Config(n), Complex());
    private static Formula PairConfig(Formula n) => Parenthesized(Seq(Parenthesized(Config(n)), Sp, Times, Sp, Parenthesized(Config(n))));
    private static Formula PairMatrix(Formula n) => Matrix(PairConfig(n), PairConfig(n), Complex());
    private static Formula Adj(Formula x) => Call("Matrix.conjTranspose", x);
    private static Formula Update(Formula x, Formula i, Formula value) => Call("Function.update", x, i, value);
    private static Formula Digit(Formula p, Formula k) => FinMk(NatMod(NatDiv(FinVal(p), Pow(D(2), k)), D(2)));
    private static Formula Block4(Formula l, Formula z) => FinMk(Add(Mul(D(2), FinVal(l)), FinVal(z)));
    private static Formula Block16(Formula l, Formula m, Formula z) => FinMk(Add(Add(Mul(D(8), FinVal(l)), Mul(D(2), FinVal(m))), FinVal(z)));
    private static Formula MiddleUpdate(Formula i, Formula x, Formula b, Formula c) => Update(Update(x, SiteAt(i, D(1)), b), SiteAt(i, D(2)), c);
    private static Formula SiteAt(Formula i, Formula k) => Call("D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.site", i, k);
    private static Formula SetList(params Formula[] values) => Seq(OpenBrace, Seq(values.SelectMany((v, i) => i == 0 ? new[] { v } : new Formula[] { Comma, Sp, v }).ToArray()), CloseBrace);
    private static Formula Filter(Formula predicate, Formula set) => Call("Finset.filter", predicate, set);
    private static Formula FinsetUniv(Formula type) => Call("Finset.univ", type);
    private static Formula MatrixSingle(Formula r, Formula c, Formula value) => Call("Matrix.single", r, c, value);

    private static Formula CzxU() => Eqn(Local("czxU"), Seq(Begin, Grp(F.Id("pmatrix")),
        D(1), Amp, D(0), Amp, D(0), Amp, D(0), RowBreak,
        D(0), Amp, D(0), Amp, D(0), Amp, D(1), RowBreak,
        D(0), Amp, D(1), Amp, D(0), Amp, D(0), RowBreak,
        D(0), Amp, D(0), Amp, D(1), Amp, D(0), End, Grp(F.Id("pmatrix"))));

    private static Formula CzxV()
    {
        Formula r = F.Id("r"), c = F.Id("c");
        Formula positive = SetList(Pair(D(0),D(0)),Pair(D(1),D(1,5)),Pair(D(2),D(2)),Pair(D(3),D(1,3)),Pair(D(4),D(4)),Pair(D(5),D(1,1)),Pair(D(6),D(6)),Pair(D(8),D(1)),Pair(D(9),D(1,4)),Pair(D(1,0),D(3)),Pair(D(1,2),D(5)),Pair(D(1,3),D(1,0)),Pair(D(1,4),D(7)),Pair(D(1,5),D(8)));
        Formula signed = new Formula.Logic(Eqn(Pair(r,c),Pair(D(7),D(9))), FormulaLogicOperator.Or, Eqn(Pair(r,c),Pair(D(1,1),D(1,2))));
        return Eqn(Local("czxV"), Lam("r", Fin(D(1,6)), Lam("c", Fin(D(1,6)), If(Mem(Pair(r,c),positive), COne(), If(signed, Neg(COne()), Cast(D(0),Complex()))))));
    }

    private static Formula MuFormula() => Eqn(Local("mu"), Div(Call("Real.sqrt", D(3)), D(4)));
    private static Formula NuFormula() => Eqn(Local("nu"), Div(Call("Real.sqrt", D(3)), D(1,6)));

    private static Formula RenormS()
    {
        Formula x=F.Id("x"), r=F.Id("r"), s=F.Id("s"), m=F.Id("m");
        Formula block = If(Eqn(DivNat(D(2),D(2),r),DivNat(D(2),D(2),s)),
            SumOver(m,Fin(D(4)), At(Mul(Mul(Local("czxV"),x),Adj(Local("czxV"))), Block16(DivNat(D(2),D(2),r),m,ModNat(D(2),D(2),r)), Block16(DivNat(D(2),D(2),s),m,ModNat(D(2),D(2),s)))),
            Cast(D(0),Complex()));
        Formula body=Mul(Mul(Adj(Local("czxU")),Call("Matrix.of",Lam("r",Fin(D(4)),Lam("s",Fin(D(4)),block)))),Local("czxU"));
        return All("x",Matrix16(),Eqn(At(Local("renormS"),x),body));
    }

    private static Formula RenormT()
    {
        Formula y=F.Id("y"), r=F.Id("r"), s=F.Id("s");
        Formula id4=Cast(D(1),Matrix4());
        Formula row=CompFin(DivNatFn(D(4),D(2)),ModNatFn(D(2),D(8)),r);
        Formula col=CompFin(DivNatFn(D(4),D(2)),ModNatFn(D(2),D(8)),s);
        Formula block=If(Eqn(DivNat(D(2),D(8),r),DivNat(D(2),D(8),s)),
            Mul(Mul(Cast(Div(Local("nu"),Local("mu")),Complex()),At(id4,row,col)),
                At(Mul(Mul(Local("czxU"),y),Adj(Local("czxU"))),Block4(DivNat(D(2),D(8),r),ModNat(D(8),D(2),r)),Block4(DivNat(D(2),D(8),s),ModNat(D(8),D(2),s)))),
            Cast(D(0),Complex()));
        Formula body=Mul(Mul(Adj(Local("czxV")),Call("Matrix.of",Lam("r",Fin(D(1,6)),Lam("s",Fin(D(1,6)),block)))),Local("czxV"));
        return All("y",Matrix4(),Eqn(At(Local("renormT"),y),body));
    }

    private static Formula LocalChannel() => All("x",Matrix16(),Eqn(At(Local("localChannel"),F.Id("x")),At(Local("renormT"),At(Local("renormS"),F.Id("x")))));

    private static Formula Site()
    {
        var n=F.Id("n"); var i=F.Id("i"); var k=F.Id("k");
        var eq=Eqn(At(Local("site"),i,k),FinMk(NatMod(Add(FinVal(i),k),n)));
        return All("n",Nat(),All("i",Fin(n),All("k",Nat(),eq)));
    }
    private static Formula WindowCode()
    {
        var n=F.Id("n"); var i=F.Id("i"); var x=F.Id("x");
        var t0=Mul(D(8),FinVal(At(x,SiteAt(i,D(0)))));
        var t1=Mul(D(4),FinVal(At(x,SiteAt(i,D(1)))));
        var t2=Mul(D(2),FinVal(At(x,SiteAt(i,D(2)))));
        var t3=FinVal(At(x,SiteAt(i,D(3))));
        var code=Add(Add(Add(t0,t1),t2),t3);
        return All("n",Nat(),All("i",Fin(n),All("x",Config(n),Eqn(At(Local("windowCode"),i,x),FinMk(code)))));
    }
    private static Formula WindowUpdate() => All("n",Nat(),All("i",Fin(F.Id("n")),All("x",Config(F.Id("n")),All("p",Fin(D(1,6)),Eqn(At(Local("windowUpdate"),F.Id("i"),F.Id("x"),F.Id("p")),Update(Update(Update(Update(F.Id("x"),SiteAt(F.Id("i"),D(0)),Digit(F.Id("p"),D(3))),SiteAt(F.Id("i"),D(1)),Digit(F.Id("p"),D(2))),SiteAt(F.Id("i"),D(2)),Digit(F.Id("p"),D(1))),SiteAt(F.Id("i"),D(3)),Digit(F.Id("p"),D(0))))))));

    private static Formula WindowChannel()
    {
        Formula n=F.Id("n"),i=F.Id("i"),a=F.Id("a"),x=F.Id("x"),y=F.Id("y"),p=F.Id("p"),q=F.Id("q");
        Formula body=SumOver(p,Fin(D(1,6)),SumOver(q,Fin(D(1,6)),Mul(At(At(Local("localChannel"),MatrixSingle(p,q,COne())),At(Local("windowCode"),i,x),At(Local("windowCode"),i,y)),At(a,At(Local("windowUpdate"),i,x,p),At(Local("windowUpdate"),i,y,q)))));
        return All("n",Nat(),All("i",Fin(n),All("a",ConfigMatrix(n),All("x",Config(n),All("y",Config(n),Eqn(At(At(At(Local("windowChannel"),n),i),a,x,y),body))))));
    }

    private static Formula WindowSuperoperator()
    {
        Formula n=F.Id("n"),i=F.Id("i"),x=F.Id("x"),y=F.Id("y");
        Formula pair=PairConfig(n);
        Formula body=At(Local("windowChannel"),n,i,MatrixSingle(Call("Prod.fst",y),Call("Prod.snd",y),COne()),Call("Prod.fst",x),Call("Prod.snd",x));
        return All("n",Nat(),All("i",Fin(n),Eqn(At(At(Local("windowSuperoperator"),n),i),Lam("x",pair,Lam("y",pair,body)))));
    }

    private static Formula ParentLindbladian()
    {
        Formula n=F.Id("n"),i=F.Id("i");
        Formula pred=Lam("i",Fin(n),Eqn(NatMod(FinVal(i),D(2)),D(0)));
        Formula domain=Filter(pred,FinsetUniv(Fin(n)));
        return All("n",Nat(),Eqn(At(Local("parentLindbladian"),n),Seq(new Formula.Subscript(Sum,Mem(i,domain)),Sp,Parenthesized(Sub(At(Local("windowSuperoperator"),n,i),Cast(D(1),PairMatrix(n)))))));
    }

    private static Formula TensorX() => All("n",Nat(),Eqn(At(Local("tensorX"),F.Id("n")),Lam("x",Config(F.Id("n")),Lam("y",Config(F.Id("n")),If(Eqn(F.Id("x"),Lam("j",Fin(F.Id("n")),Add(At(F.Id("y"),F.Id("j")),D(1)))),COne(),Cast(D(0),Complex()))))));
    private static Formula Cz() => All("n",Nat(),Eqn(At(Local("cz"),F.Id("n")),Call("Matrix.diagonal",Lam("x",Config(F.Id("n")),Pow(Neg(COne()),SumOver(F.Id("j"),Fin(F.Id("n")),Mul(FinVal(At(F.Id("x"),F.Id("j"))),FinVal(At(F.Id("x"),SiteAt(F.Id("j"),D(1)))))))))));
    private static Formula CzxUnitary() => All("n",Nat(),Eqn(At(Local("czxUnitary"),F.Id("n")),Mul(At(Local("cz"),F.Id("n")),At(Local("tensorX"),F.Id("n")))));
    private static Formula Evolution()
    {
        Formula n=F.Id("n"),t=F.Id("t"),a=F.Id("a"),x=F.Id("x"),y=F.Id("y"),p=F.Id("p");
        Formula vector=Lam("p",PairConfig(n),At(a,Call("Prod.fst",p),Call("Prod.snd",p)));
        Formula body=At(Call("Matrix.mulVec",Call("NormedSpace.exp",Smul(Cast(t,Complex()),At(Local("parentLindbladian"),n))),vector),Pair(x,y));
        return All("n",Nat(),All("t",Real(),All("a",ConfigMatrix(n),All("x",Config(n),All("y",Config(n),Eqn(At(Local("evolution"),n,t,a,x,y),body))))));
    }
    private static Formula Gauge() => All("n",Nat(),All("e",Fin(D(2)),All("x",Config(F.Id("n")),Eqn(At(Local("gauge"),F.Id("n"),F.Id("e"),F.Id("x")),Pow(Neg(COne()),Mul(FinVal(F.Id("e")),SumOver(F.Id("j"),Fin(F.Id("n")),Mul(FinVal(At(F.Id("x"),F.Id("j"))),FinVal(At(F.Id("x"),SiteAt(F.Id("j"),D(1))))))))))));
    private static Formula SiteInjective() => All("n",Nat(),Imp(Le(D(4),F.Id("n")),All("i",Fin(F.Id("n")),All("k",Fin(D(4)),All("l",Fin(D(4)),Iff(Eqn(SiteAt(F.Id("i"),FinVal(F.Id("k"))),SiteAt(F.Id("i"),FinVal(F.Id("l")))),Eqn(F.Id("k"),F.Id("l"))))))));
    private static Formula WindowLM()
    { var n=F.Id("n"); var i=F.Id("i"); var a=F.Id("a"); var eq=Eqn(At(At(Local("windowLM"),n,i),a),At(Local("windowChannel"),n,i,a)); return All("n",Nat(),All("i",Fin(n),All("a",ConfigMatrix(n),eq))); }
    private static Formula GoodWindow()
    { var n=F.Id("n"); var i=F.Id("i"); var d=Delta; var k=F.Id("k"); var pred=All("k",Fin(D(4)),Eqn(At(d,SiteAt(i,FinVal(k))),At(d,i))); return All("n",Nat(),All("i",Fin(n),All("δ",Config(n),Eqn(At(Local("goodWindow"),i,d),pred)))); }
    private static Formula SectorGauge()
    { var n=F.Id("n"); var d=Delta; var x=F.Id("x"); var j=F.Id("j"); var edge=Mul(Mul(FinVal(At(d,j)),FinVal(At(x,j))),FinVal(At(x,SiteAt(j,D(1))))); var rhs=Pow(Neg(COne()),SumOver(j,Fin(n),edge)); return All("n",Nat(),All("δ",Config(n),All("x",Config(n),Eqn(At(Local("sectorGauge"),n,d,x),rhs)))); }
    private static Formula GaugedUnit()
    { var n=F.Id("n"); var d=Delta; var x=F.Id("x"); var rhs=Smul(At(Local("sectorGauge"),n,d,x),MatrixSingle(Add(x,d),x,COne())); return All("n",Nat(),All("δ",Config(n),All("x",Config(n),Eqn(At(Local("gaugedUnit"),n,d,x),rhs)))); }
    private static Formula SectorGaugeConst()
    { var n=F.Id("n"); var e=F.Id("e"); var x=F.Id("x"); var constant=Const(Fin(n),e); return All("n",Nat(),All("e",Fin(D(2)),All("x",Config(n),Eqn(At(Local("sectorGauge"),n,constant,x),At(Local("gauge"),n,e,x))))); }
    private static Formula SectorGaugeMulSelf()
    { var n=F.Id("n"); var d=Delta; var x=F.Id("x"); var phase=At(Local("sectorGauge"),n,d,x); return All("n",Nat(),All("δ",Config(n),All("x",Config(n),Eqn(Mul(phase,phase),COne())))); }
    private static Formula SiteSuccInjective() { var n=F.Id("n"); return All("n",Nat(),Call("Function.Injective",Lam("i",Fin(n),SiteAt(F.Id("i"),D(1))))); }
    private static Formula GaugedWindowSector()
    { var n=F.Id("n"); var i=F.Id("i"); var d=Delta; var x=F.Id("x"); var b=F.Id("b"); var c=F.Id("c"); var sum=SumOver(b,Fin(D(2)),SumOver(c,Fin(D(2)),At(Local("gaugedUnit"),n,d,MiddleUpdate(i,x,b,c)))); var rhs=If(At(Local("goodWindow"),i,d),Smul(Inv(Cast(D(4),Complex())),sum),Cast(D(0),ConfigMatrix(n))); var eq=Eqn(At(Local("windowChannel"),n,i,At(Local("gaugedUnit"),n,d,x)),rhs); return All("n",Nat(),Imp(Le(D(4),n),All("i",Fin(n),All("δ",Config(n),All("x",Config(n),eq))))); }
    private static Formula MatrixLinearMapExtGauged()
    { var n=F.Id("n"); var f=F.Id("f"); var g=F.Id("g"); var d=Delta; var x=F.Id("x"); var hu=Eqn(At(f,At(Local("gaugedUnit"),n,d,x)),At(g,At(Local("gaugedUnit"),n,d,x))); var hyp=All("δ",Config(n),All("x",Config(n),hu)); return All("n",Nat(),All("f",Call("Module.End",Complex(),ConfigMatrix(n)),All("g",Call("Module.End",Complex(),ConfigMatrix(n)),Imp(hyp,Eqn(f,g))))); }
    private static Formula WindowChannelsCommute()
    { var n=F.Id("n"); var i=F.Id("i"); var j=F.Id("j"); var a=F.Id("a"); var lhs=At(Local("windowChannel"),n,i,At(Local("windowChannel"),n,j,a)); var rhs=At(Local("windowChannel"),n,j,At(Local("windowChannel"),n,i,a)); return All("n",Nat(),Imp(Le(D(4),n),All("i",Fin(n),All("j",Fin(n),All("a",ConfigMatrix(n),Eqn(lhs,rhs)))))); }
    private static Formula WindowSuperoperatorAction()
    { var n=F.Id("n"); var i=F.Id("i"); var a=F.Id("a"); var x=F.Id("x"); var y=F.Id("y"); var p=F.Id("p"); var vec=Lam("p",PairConfig(n),At(a,Call("Prod.fst",p),Call("Prod.snd",p))); var lhs=At(Call("Matrix.mulVec",At(Local("windowSuperoperator"),n,i),vec),Pair(x,y)); var rhs=At(Local("windowChannel"),n,i,a,x,y); return All("n",Nat(),All("i",Fin(n),All("a",ConfigMatrix(n),All("x",Config(n),All("y",Config(n),Eqn(lhs,rhs)))))); }
    private static Formula WindowIdempotent()
    { var n=F.Id("n"); var i=F.Id("i"); var p=Call("IsIdempotentElem",At(Local("windowSuperoperator"),n,i)); return All("n",Nat(),Imp(Le(D(4),n),All("i",Fin(n),p))); }
}
