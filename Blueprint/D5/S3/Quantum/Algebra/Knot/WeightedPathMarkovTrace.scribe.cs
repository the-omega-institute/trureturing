using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class WeightedPathMarkovTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Perron path algebras admit a trace-preserving tower and an exact last-generator compression law.",
        H("Weighted Path Tower and Markov Trace"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-path-markov-trace"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.weighted_path_markov_trace"),
            H("The actual finite path tower"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let L be a finite vertex type, R a symmetric decidable relation, d a strictly positive real weight at every vertex, and delta a strictly positive real number. Assume the Perron equality sum of d(u) over R(t,u) equals delta d(t) at every t. Fix a start s. P(n,s,t) is the literal LegalPath R n s t of WeightedLegalPathTemperleyLieb; C(n,s) is the product over t of complex matrices on P(n,s,t). Empty endpoint fibers are included.")),
                Paragraph(Text("Appending the last edge t to u gives an injective map a(t,u) from P(n,s,t) into P(n+1,s,u). The rectangular matrix J(t,u) has entry one at (a(t,u)(x),x), and zero elsewhere. Splitting a long path into its predecessor endpoint and prefix identifies P(n+1,s,u) with the disjoint union of P(n,s,t) over R(t,u). In these coordinates iota(X) is the block diagonal matrix with blocks X(t). The compression F(Y)(t) is the sum over R(t,u) of d(u)/(delta d(t)) times J(t,u) conjugate-transpose Y(u) J(t,u).")),
                Paragraph(Text("The trace is tau(n,s)(X) = sum over t of d(t) trace(X(t)), divided by delta to the n times d(s). The theorem proves the append decomposition, the unital faithful star algebra inclusion, retraction and bimodule law of compression, trace preservation and normalization. For n positive, e(n) in C(n+1,s) is the exact old pathProjection R d delta (n+1) s t n in each endpoint block. Its compressed kernel vanishes off the diagonal. On a diagonal prefix, only the neighbor equal to the preceding vertex survives, and its Perron weight cancels the local denominator to give delta to the minus two.")),
                Paragraph(Text("In the displayed statement, FinitePerronData denotes precisely the hypotheses above. DistinctLegalPredecessors(t,v,u) means t differs from v and both R(t,u) and R(v,u) hold. Adjoint is conjugate transpose, block(Y,u) is Y(u), and appendSubmatrix(Y,t,u) has entry Y(u)(a(t,u)(x),a(t,u)(y)). UnitalInjectiveStarAlgebraInclusion means an injective complex-linear algebra homomorphism preserving one and adjoint. Positive(n) means zero is less than n.")),
                Paragraph(Text("The local Temperley-Lieb relations are reused from weighted_legal_path_temperley_lieb. Trace compatibility requires the additional finite predecessor-fiber reindexing and Perron equality. The tower and trace begin at n=0; the last-generator identity begins at n=1. No connectedness or nonempty-fiber assumption is made.")),
                Paragraph(Text("This is classical path-model background. Aharonov, Jones and Landau, A Polynomial Quantum Algorithm for Approximating the Jones Polynomial, arXiv:quant-ph/0511096v2, Definition 3.3 and Claim 3.6, give the explicit line-graph endpoint trace and its local Markov calculation. AJL uses unnormalized Temperley-Lieb generators with Markov coefficient one over delta. Multiplying the present literal projection by delta recovers that normalization, so its Markov coefficient is one over delta squared. Here the statement treats arbitrary finite positive Perron data and the entire endpoint-block algebra. This tower does not construct a geometric closure map, prove geometric Markov equivalence, or produce a knot with a prescribed Jones polynomial."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-path-tau-scalar-linearity"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.tau_smul"),
                H("Scalar linearity of the same endpoint trace"),
                StatementSource.FromAuthor(ScalarStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite decidable L, arbitrary relation R, real weights d and real delta, every n and start s, every complex c and every X in C(R,n,s), tau(c times X) equals c tau(X). Positivity, symmetry and the Perron equality are not needed for this scalar identity. The Artin and signed Markov proofs consume this scalar-linearity helper at its source owner. It follows from matrix-trace scalar linearity and finite-sum distribution; it is a consumed helper rather than new independent mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-path-split-append"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.split_append_coordinates"),
                H("Splitting an appended legal path"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite decidable L, relation R, natural n, endpoints s,t,u, edge R(t,u) and x in LegalPath(R,n,s,t), splitPath of append(x,u) is the sigma pair of the legal predecessor t and x. This is the original private proof exposed through a directly consumed alias, retaining its frozen private identity for the returning-block matrix-unit proof; it is a consumed helper and makes no independent mathematical claim."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-path-append-injective"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.append_isInjective"),
                H("Appending preserves path distinctions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite decidable L, relation R, natural n, endpoints s,t,u and legal edge R(t,u), append from LegalPath(R,n,s,t) to LegalPath(R,n+1,s,u) is injective. The existing proof is exposed through a directly consumed alias and its frozen private identity is retained and consumed by the returning-block matrix-unit proof. No positivity, symmetry or Perron condition is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-path-iota-append"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.iota_append_entry"),
                H("The inclusion in literal append coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite decidable L, relation R, natural n, endpoints s,t,u, legal edge R(t,u), X in the full C(R,n,s), and x,y in LegalPath(R,n,s,t), the u-block entry of iota(X) at append(x,u),append(y,u) equals X(t)(x,y). This is the original private proof exposed through a directly consumed alias, retaining its frozen private identity and directly consumed by the new returning-block derivation. It is a helper, not an independent formalization gain."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula EqTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula ScalarStatement()
    {
        Formula n = F.Id("n"), s = F.Id("s"), c = F.Id("c"), x = F.Id("X");
        Formula law = EqTo(Call("tau", n, s, Call("SMul", c, x)),
            Mul(c, Call("tau", n, s, x)));
        return Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))), All("s", F.Id("L"),
            All("c", Seq(Mathbb, Grp(F.Id("C"))), All("X", Call("C", n, s), law)))));
    }
    private static Formula Statement()
    {
        Formula n = F.Id("n"), s = F.Id("s"), x = F.Id("X"), y = F.Id("Y"), a = F.Id("A"), b = F.Id("B"), delta = F.Id("delta");
        Formula t = F.Id("t"), u = F.Id("u"), v = F.Id("v"), labels = F.Id("L");
        Formula c = Call("C", n, s), next = Call("C", Seq(n, Plus, D(1)), s);
        Formula inclusion(Formula z) => Call("iota", n, s, z);
        Formula compression(Formula z) => Call("F", n, s, z);
        Formula trace(Formula z) => Call("tau", n, s, z);
        Formula nextTrace(Formula z) => Call("tau", Seq(n, Plus, D(1)), s, z);
        Formula adjoint(Formula z) => Call("adjoint", z);
        Formula jt = Call("J", t, u), jv = Call("J", v, u), e = Call("e", n);
        Formula inverseSquare = new Formula.Fraction(D(1), Seq(delta, Caret, Grp(D(2))));
        Formula lastLaws = Seq(
            EqTo(compression(e), Mul(inverseSquare, D(1))), Semi, Sp,
            All("X", c, EqTo(nextTrace(Mul(inclusion(x), e)), Mul(inverseSquare, trace(x)))), Semi, Sp,
            EqTo(adjoint(e), e), Semi, Sp, EqTo(Mul(e, e), e));
        Formula laws = Seq(
            Call("UnitalInjectiveStarAlgebraInclusion", Call("iota", n, s)), RowBreak,
            All("t", labels, All("u", labels, Seq(Call("R", t, u), Rightarrow, Sp,
                EqTo(Mul(adjoint(jt), jt), D(1))))), RowBreak,
            All("t", labels, All("v", labels, All("u", labels, Seq(
                Call("DistinctLegalPredecessors", t, v, u), Rightarrow, Sp,
                EqTo(Mul(adjoint(jt), jv), D(0)))))), RowBreak,
            All("t", labels, All("u", labels, All("Y", next, Seq(
                Call("R", t, u), Rightarrow, Sp,
                EqTo(Mul(Mul(adjoint(jt), Call("block", y, u)), jt), Call("appendSubmatrix", y, t, u)))))), RowBreak,
            All("X", c, EqTo(compression(inclusion(x)), x)), Semi, Sp,
            All("Y", next, EqTo(trace(compression(y)), nextTrace(y))), RowBreak,
            All("A", c, All("B", c, All("Y", next,
                EqTo(compression(Mul(Mul(inclusion(a), y), inclusion(b))), Mul(Mul(a, compression(y)), b))))), RowBreak,
            All("X", c, EqTo(nextTrace(inclusion(x)), trace(x))), Semi, Sp,
            EqTo(trace(D(1)), D(1)), RowBreak,
            Call("Positive", n), Rightarrow, Sp, Open, lastLaws, Close);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Call("FinitePerronData", labels, F.Id("R"), F.Id("d"), delta), RowBreak,
            All("n", Seq(Mathbb, Grp(F.Id("N"))), All("s", labels, laws)),
            End, Grp(F.Id("gathered"))));
    }
}
