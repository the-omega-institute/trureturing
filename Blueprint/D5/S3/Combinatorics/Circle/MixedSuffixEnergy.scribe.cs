using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class MixedSuffixEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula k = V("k"), t = V("t"), p = V("p"), x = V("x"), m = V("m"),
            A = V("A"), B = V("B"), j = V("j"), n = V("n");
        Formula W = Call("append", A, Call("cons", x, B));
        Formula P = Call("path", p, m), Vnew = Call("append", A, P);
        Formula s0 = Call("actualSource", k, t, p), source = Call("actualSource", k, t);
        Formula ell = Call("largeUsed", k, t, B), small = Call("smallUsed", k, t, B);
        Formula label = Call("phase", p, j), C = Call("half", k);
        Formula sw = Call("toFinset", W), sp = Call("toFinset", P), sv = Call("toFinset", Vnew);
        Formula returned = Call("insert", x, Call("toFinset", B));
        Formula oldRemaining = Call("compl", sw), newRemaining = Call("compl", sv);
        Formula prefix = Call("mass", source, Call("take", n, Vnew));
        Formula gv = Call("G", k, t, Vnew), gw = Call("G", k, t, W);
        Formula uv = Call("U", Vnew), uw = Call("U", W);
        Formula assumptions = And(Le(Num(3), k), Le(Num(2), m),
            Eq(Call("mod", m, Num(2)), Num(0)), Call("Nodup", W),
            Call("InStrip", source, C, Num(0), W), Eq(Call("phase", p, m), x),
            Q(Imp(Lt(j, m), And(Call("NotMem", label, W), Call("Large", k, t, label))), ("j", Name("Nat"))),
            Lt(Num(0), Sub(Mul(Num(3), Call("abs", s0)), Call("modulus", k))),
            Le(ell, Sub(m, Num(1))));
        Formula conclusion = And(Lt(m, k), Call("Nodup", P), Call("ListDisjoint", P, W),
            Call("Nodup", Vnew), Call("InStrip", source, C, Num(0), Vnew),
            Q(And(Le(Num(0), prefix), Le(prefix, C)), ("n", Name("Nat"))),
            Eq(sv, Call("union", Call("sdiff", sw, returned), sp)),
            Call("Disjoint", Call("sdiff", sw, returned), sp),
            Eq(newRemaining, Call("union", Call("sdiff", oldRemaining, sp), returned)),
            Call("Disjoint", Call("sdiff", oldRemaining, sp), returned),
            Eq(Add(gv, m), Add(Add(gw, Num(1)), ell)),
            Eq(Add(uv, m), Add(Add(uw, Num(1)), Call("length", B))),
            Lt(Call("H", k, t, Vnew), Call("H", k, t, W)),
            Eq(Call("remainingMass", source, Vnew), Call("neg", Call("mass", source, Vnew))),
            Imp(Eq(ell, Sub(m, Num(1))), And(Eq(gv, gw), Eq(uv, Add(uw, small)))),
            Imp(Le(ell, Sub(m, Num(2))), Lt(gv, gw)),
            Lt(Call("J", k, t, Vnew), Call("J", k, t, W)));
        Formula wordType = Call("List", Call("Fin", k));
        Formula statement = Q(Imp(assumptions, conclusion), ("k", Name("Nat")),
            ("t", Name("Nat")), ("p", Call("Fin", k)), ("x", Call("Fin", k)),
            ("m", Name("Nat")), ("A", wordType), ("B", wordType));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Mixed suffix exchange: a native even expanding unused path can replace a consumed label and its mixed suffix, with full physical bookkeeping and strict (G,H,U) descent when the suffix has at most m-1 LARGE labels.",
            H("Energy before SMALL count: the physical mixed-suffix exchange"),
            Blocks(
                Describe.Lean(DescribeId.Create("physical-mixed-suffix-energy-exchange"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Circle/MixedSuffixEnergy.mixed_suffix_energy_exchange"),
                    H("The explicit exchange and both descent cases"),
                    StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("All labels live in the original Fin(k), and s is SourceWidth.actualSource. W=A++[x]++B is a legal distinct-label word. The literal modulo-k successor path of even length m>=2 consists of unused LARGE labels and enters x. The sole expanding condition is d=3*|s(p)|-N>0; sign orientation is selected inside the proof. LARGE means |s|>=Q, SMALL means |s|<=Q-1, where Q=2^(k-2), N=4Q-1, C=N/2. There is no append-blocking, suffix-repair, endpoint, minimizer, or replacement-energy hypothesis.")),
                        Paragraph(Text("G is the sum of LARGE indicators over the actual unused physical complement. U is its cardinality, expressed as a sum of ones. H is the sum of 3^|s| over consumed LARGE occurrences. smallUsed(B) and largeUsed(B) partition the literal suffix labels, rather than a quotient by numerical values. Their sum is B.length. J is the standard natural lexicographic triple (G,H,U), using mathlib's nested Lex product.")),
                        Paragraph(Text("The new word is exactly V=A++path. If m>=k, the earlier index m mod k reaches the consumed terminal physical label, contradicting unusedness. Thus m<k; modular cancellation proves path.Nodup, and unusedness proves disjointness from all of W. The proof derives both used and unused partitions and the disjointness of both displayed unions. Equal source values, nonunits, and short numerical orbits never merge labels or energy multiplicities.")),
                        Paragraph(Text("ExpandingSourcePath supplies 0<=F_j<=r for every natural take and sum_path 3^|s| < 3^r. If x is positive, old legality bounds a between 0 and C-r. If x is negative, it bounds a between r and C. Every inserted height therefore lies between the original departure and arrival heights of x. The unchanged prefix A is then appended to this proved path. Empty and overlength takes are included through InStrip and min(n,m), with no endpoint-only shortcut.")),
                        Paragraph(Text("The exact natural balances are G(V)+m=G(W)+1+largeUsed(B) and U(V)+m=U(W)+1+B.length. H(A) cancels, and the inserted energy is strictly below the returned contribution of x alone; all returned LARGE terms of B are nonnegative. For largeUsed(B)=m-1, this gives G(V)=G(W), H(V)<H(W), U(V)=U(W)+smallUsed(B). If largeUsed(B)<=m-2, the same explicit V strictly lowers G. The suffix SMALL labels may have any signs and positions and may all be returned. Moving H before U is what makes their returned count compatible with strict descent.")),
                        Paragraph(Text("The new complement sum is minus the new endpoint, using the existing physical zero-total theorem ZeroSumSubsets.source_cycle and the new literal complement, not an assumed inventory partition. The proof never invokes SMALL ORDERING on a LARGE batch. It uses no minimizer wrapper, no assumption of completion, no new axiom or proof placeholder.")),
                        Paragraph(Text("The universal availability gap remains: no theorem here forces such an eligible even expanding path or such a short LARGE suffix at every hypothetical incomplete global minimizer. The case with two later opposite-sign LARGE labels still needs an actual SMALL-subset gate, and deeper suffixes or isolated/SMALL source boundaries need further constructions. E_keep_one is optional and is not included in this candidate. d=0 and k<3 are outside this exchange theorem. An all-zero source cannot satisfy d>0; this theorem supplies no separate zero-source completion claim. Seam crossings, ties, short numerical periods, and nonunits carry no extra hypotheses. Full C3.1 remains OPEN."))),
                    DescribeRole.Theorem)), []));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Name(string s) => new Formula.NamedConstant(FormulaIdentifier.Create(s));
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Call(string s, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] vs)
    {
        for (var i = vs.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(vs[i].Name), vs[i].Domain, body);
        return body;
    }
    private static Formula And(params Formula[] a)
    {
        var body = a[^1];
        for (var i = a.Length - 2; i >= 0; --i) body = new Formula.Logic(a[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
