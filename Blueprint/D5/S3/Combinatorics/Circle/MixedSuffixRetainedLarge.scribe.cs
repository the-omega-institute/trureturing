using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class MixedSuffixRetainedLargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula k = V("k"), t = V("t"), p = V("p"), x = V("x"), m = V("m"),
            A = V("A"), B = V("B"), z = V("z"), j = V("j"), n = V("n");
        Formula source = Call("actualSource", k, t), C = Call("half", k);
        Formula sp = Call("actualSource", k, t, p), sx = Call("actualSource", k, t, x),
            sz = Call("actualSource", k, t, z);
        Formula W = Call("append", A, Call("cons", x, B));
        Formula P = Call("path", p, m), V0 = Call("append", A, P);
        Formula Vnew = Call("append", V0, Call("singleton", z));
        Formula b = Call("mass", source, V0), final = Add(b, sz);
        Formula sw = Call("toFinset", W), sv = Call("toFinset", Vnew), ps = Call("toFinset", P);
        Formula returned = Call("insert", x, Call("sdiff", Call("toFinset", B), Call("singleton", z)));
        Formula oldRemaining = Call("compl", sw), newRemaining = Call("compl", sv);
        Formula prefix = Call("mass", source, Call("take", n, Vnew));
        Formula label = Call("phase", p, j);
        Formula gv = Call("G", k, t, Vnew), gw = Call("G", k, t, W);
        Formula hv = Call("H", k, t, Vnew), hw = Call("H", k, t, W);
        Formula uv = Call("U", Vnew), uw = Call("U", W);
        Formula assumptions = And(Le(Num(3), k), Le(Num(2), m),
            Eq(Call("mod", m, Num(2)), Num(0)), Call("Nodup", W),
            Call("InStrip", source, C, Num(0), W), Eq(Call("phase", p, m), x),
            Q(Imp(Lt(j, m), And(Call("NotMem", label, W), Call("Large", k, t, label))),
                ("j", Name("Nat"))),
            Lt(Num(0), Sub(Mul(Num(3), Call("abs", sp)), Call("modulus", k))),
            Eq(Call("largeUsed", k, t, B), m), Call("Mem", z, B), Call("Large", k, t, z),
            Lt(Num(0), Mul(sp, sz)), Le(Call("abs", sz), Call("abs", sp)));
        Formula conclusion = And(Lt(m, k), Call("Nodup", P), Call("ListDisjoint", P, W),
            Call("Nodup", Vnew), Eq(Call("mass", source, P), Sub(sx, sp)),
            Call("InStrip", source, C, b, Call("singleton", z)),
            And(Le(Num(0), final), Le(final, C)),
            Call("InStrip", source, C, Num(0), Vnew),
            Q(And(Le(Num(0), prefix), Le(prefix, C)), ("n", Name("Nat"))),
            Eq(sv, Call("union", Call("sdiff", sw, returned), ps)),
            Call("Disjoint", Call("sdiff", sw, returned), ps),
            Eq(newRemaining, Call("union", Call("sdiff", oldRemaining, ps), returned)),
            Call("Disjoint", Call("sdiff", oldRemaining, ps), returned),
            Eq(gv, gw),
            Eq(Add(Add(hv, Pow(Num(3), Call("natAbs", sx))), Call("H", k, t, Call("erase", B, z))),
                Add(hw, Call("H", k, t, P))),
            Lt(hv, hw), Eq(Add(uv, m), Add(uw, Call("length", B))),
            Eq(uv, Add(uw, Call("smallUsed", k, t, B))),
            Eq(Call("remainingMass", source, Vnew), Call("neg", Call("mass", source, Vnew))),
            Lt(Call("J", k, t, Vnew), Call("J", k, t, W)));
        Formula wordType = Call("List", Call("Fin", k));
        Formula statement = Q(Imp(assumptions, conclusion), ("k", Name("Nat")),
            ("t", Name("Nat")), ("p", Call("Fin", k)), ("x", Call("Fin", k)),
            ("m", Name("Nat")), ("A", wordType), ("B", wordType), ("z", Call("Fin", k)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Retained LARGE exchange: retain an actual later same-sign LARGE after a native even expanding path, deriving its new gate and strict (G,H,U) descent with exact physical inventory.",
            H("Moving one LARGE label across an arbitrary mixed suffix"),
            Blocks(
                Describe.Lean(DescribeId.Create("physical-mixed-suffix-retained-large-exchange"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Circle/MixedSuffixRetainedLarge.mixed_suffix_retained_large_exchange"),
                    H("E_keep_one with the proved singleton gate and exact energy cancellation"),
                    StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("The source is SourceWidth.actualSource on physical Fin(k), with k>=3, N=2^k-1 and C=N/2. LARGE means 2^(k-2)<=|s|. W=A++[x]++B is Nodup and legal from zero at capacity C. The actual modulo-k path from p has even length m>=2, consists of unused LARGE labels, and enters consumed x. d=3*|s(p)|-N is strictly positive. The suffix has exactly m LARGE labels and arbitrarily many SMALL labels in arbitrary positions. A physical z in B is LARGE, s(p)*s(z)>0, and |s(z)|<=|s(p)|. No minimizer, availability, endpoint, legal new gate, energy drop, or suffix viability is a hypothesis.")),
                        Paragraph(Text("The delivered word is literally V=(A++path)++[z]. The proof consumes MixedSuffixEnergy.mixed_suffix_energy_exchange on the truncated legal old word A++[x], with an empty suffix. This supplies m<k, path.Nodup, legality of V0=A++path for every natural take, and H(V0)<H(A++[x]). It does not apply E_mix's m-1 bound to the present m-LARGE suffix B. Unusedness in the full W separately proves disjointness from every physical old label, hence z is moved once and V remains Nodup.")),
                        Paragraph(Text("The extra consumed helper unsigned_path_sum uses the existing SourceWidth.unsigned_step, ExpandingSourcePath.phase_step, SourceWidth.path_range and SourceWidth.path_sum. The unsigned potential is u(q)=s(q)+N when s(q)<0 and u(q)=s(q) otherwise. It gives sum(path)=u(x)-u(p) on the actual physical path, including the seam. ExpandingSourcePath.expanding_path_estimates, with orientation chosen from the sign of s(p), forces x to have that same sign and to be LARGE. The unsigned corrections therefore cancel, proving sum(path)=s(x)-s(p), rather than assuming this identity or duplicating the source profile proof.")),
                        Paragraph(Text("Put a=sum(A) and b=sum(V0). The proved endpoint gives b+s(p)=a+s(x), while old legality bounds a+s(x) in [0,C] and the inherited path proof bounds b in [0,C]. For s(p)>0 the sign condition gives s(z)>0 and the magnitude bound gives s(z)<=s(p), so 0<=b+s(z)<=b+s(p)<=C. For s(p)<0 it gives s(z)<0 and s(p)<=s(z), so 0<=b+s(p)<=b+s(z)<=b<=C. This is the real singleton LARGE gate at its new position. Intervening SMALL or LARGE labels in old B supply no premise. Appending this singleton proves InStrip and all-natural zero-start prefix bounds, including empty and overlength takes.")),
                        Paragraph(Text("Let R={x} union (B.toFinset minus {z}), S=W.toFinset and I=path.toFinset. The exact used partition is (S minus R) union I; the exact unused partition is (S complement minus I) union R. Both displayed unions are proved disjoint. Thus only z is retained from B, x is returned, and every other suffix occurrence is returned. All equal values and short numerical orbits still count as separate Fin(k) labels. No unit, numerical-injectivity, full numerical-period, seam, or tie exception is introduced.")),
                        Paragraph(Text("MixedSuffixEnergy.G, H, U, J, largeUsed and smallUsed are reused unchanged. Each inserted label is LARGE, so largeUsed(path)=m. With x and z both LARGE, equality largeUsed(B)=m and physical conservation prove G(V)=G(W). Exact cardinality conservation proves U(V)+m=U(W)+B.length and therefore U(V)=U(W)+smallUsed(B). Nodup makes these list-weight calculations physical set inventories. The native zero-total source_cycle also gives the new complement sum equal to minus the new endpoint.")),
                        Paragraph(Text("The retained term cancels using the actual physical permutation B ~ z::B.erase(z), not by identifying equal numerical values. The proof exports H(V)+3^|s(x)|+H(B.erase(z))=H(W)+H(path). The inherited source energy bound implies H(V0)<H(A++[x]); adding the same retained term and the nonnegative returned energy yields H(V)<H(W). Hence the first coordinate of the natural lexicographic J=(G,H,U) is equal and the second strictly decreases even though returning SMALL labels may increase U.")),
                        Paragraph(Text("This is a conditional exchange for arbitrary even m and arbitrary mixed B. The numerical k=10,t=360 control is used only as a transient nonvacuity calculation, with no additional canonical numerical theorem. Full C3.1, universal exchange availability, and arbitrary-tail continuation remain OPEN. In particular the two later opposite-sign LARGE case still needs an actual physical SMALL-subset departure gate or a different exchange. k<3 and d=0 are outside the theorem; zeros cannot satisfy its strict same-sign retained-label hypothesis."))),
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
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
