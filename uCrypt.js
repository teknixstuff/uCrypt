(function() {
    "use strict";

    var prototype = "prototype";
    var length = "length";
    var onreadystatechange = "onreadystatechange";
    var mathFloor = Math['floor'];
    var mathPow = Math['pow'];
    var mathLog = Math['log'];

    var BigInteger = (function() {
        if (typeof BigInt !== 'undefined') {
            var BigInteger = function(val) { return BigInt(val); };
            BigInteger.add = function(a, b) { return a + b; };
            BigInteger.subtract = function(a, b) { return a - b; };
            BigInteger.multiply = function(a, b) { return a * b; };
            BigInteger.divide = function(a, b) { return a / b; };
            BigInteger.remainder = function(a, b) { return a % b; };
            BigInteger.exponentiate = Function('a', 'b', 'return a ** b;');
            BigInteger.leftShift = function(a, b) { return a << b; };
            BigInteger.signedRightShift = function(a, b) { return a >> b; };
            BigInteger.bitwiseAnd = function(a, b) { return a & b; };
            BigInteger.bitwiseOr = function(a, b) { return a | b; };
            BigInteger.bitwiseXor = function(a, b) { return a ^ b; };
            BigInteger.unaryMinus = function(a) { return -a; };
            BigInteger.bitwiseNot = function(a) { return ~a; };
            BigInteger.equal = function(a, b) { return a === b; };
            BigInteger.notEqual = function(a, b) { return a !== b; };
            BigInteger.lessThan = function(a, b) { return a < b; };
            BigInteger.lessThanOrEqual = function(a, b) { return a <= b; };
            BigInteger.greaterThan = function(a, b) { return a > b; };
            BigInteger.greaterThanOrEqual = function(a, b) { return a >= b; };
            return BigInteger;
        }

        var parseInteger = function(s, from, to, radix) {
            var i = from - 1;
            var n = 0;
            var y = radix < 10 ? radix : 10;
            while (++i < to) {
                var code = s.charCodeAt(i);
                var v = code - "0".charCodeAt(0);
                if (v < 0 || y <= v) {
                    v = 10 - "A".charCodeAt(0) + code;
                    if (v < 10 || radix <= v) {
                        v = 10 - "a".charCodeAt(0) + code;
                        if (v < 10 || radix <= v) {
                            throw new RangeError();
                        }
                    }
                }
                n = n * radix + v;
            }
            return n;
        };

        var createArray = function(length) {
            var x = new Array(length);
            var i = -1;
            while (++i < length) {
                x[i] = 0;
            }
            return x;
        };

        var epsilon = 2 / (9007199254740991 + 1);
        while (1 + epsilon / 2 !== 1) {
            epsilon /= 2;
        }
        var BASE = 2 / epsilon;
        var s = 134217728;
        while (s * s < 2 / epsilon) {
            s *= 2;
        }
        var SPLIT = s + 1;
        var BASELOG2 = Math['ceil'](mathLog(BASE) / mathLog(2));

        var fma = function(a, b, product) {
            var at = SPLIT * a;
            var ahi = at - (at - a);
            var alo = a - ahi;
            var bt = SPLIT * b;
            var bhi = bt - (bt - b);
            var blo = b - bhi;
            var error = ((ahi * bhi + product) + ahi * blo + alo * bhi) + alo * blo;
            return error;
        };

        var fastTrunc = function(x) {
            var v = (x - BASE) + BASE;
            return v > x ? v - 1 : v;
        };

        var performMultiplication = function(carry, a, b) {
            var product = a * b;
            var error = fma(a, b, -product);

            var hi = (product / BASE) - BASE + BASE;
            var lo = product - hi * BASE + error;

            if (lo >= 0) {
                lo -= BASE;
                hi += 1;
            }

            lo += carry;
            if (lo < 0) {
                lo += BASE;
                hi -= 1;
            }

            return {
                lo: lo,
                hi: hi
            };
        };

        var performDivision = function(a, b, divisor) {
            if (a >= divisor) {
                throw new RangeError();
            }
            var p = a * BASE;
            var q = fastTrunc(p / divisor);

            var r = 0 - fma(q, divisor, -p);
            if (r < 0) {
                q -= 1;
                r += divisor;
            }

            r += b - divisor;
            if (r < 0) {
                r += divisor;
            } else {
                q += 1;
            }
            var y = fastTrunc(r / divisor);
            r -= y * divisor;
            q += y;
            return {
                q: q,
                r: r
            };
        };

        var INTERNAL = {};

        var BigInteger = function (value, sign, magnitude, length) {
            if (value === INTERNAL) {
                this.sign = sign;
                this.magnitude = magnitude;
                this.length = length;
                return;
            }
            if (typeof value === "number") {
                return fromNumber(value);
            }
            if (typeof value === "string") {
                return fromString(value);
            }
            if (typeof value === "bigint") {
                return fromString(value.toString());
            }
            if (value instanceof BigInteger) {
                return value;
            }
            if (typeof value === "boolean") {
                return fromNumber(Number(value));
            }
            throw new RangeError();
        };

        var createBigInteger = function(sign, magnitude, length) {
            return new BigInteger(INTERNAL, sign, magnitude, length);
        };

        var fromHugeNumber = function(n) {
            var sign = n < 0 ? 1 : 0;
            var a = n < 0 ? 0 - n : 0 + n;
            if (a === 1 / 0) {
                throw new RangeError();
            }
            var i = 0;
            while (a >= mathPow(BASE, 2)) {
                a /= BASE;
                i += 1;
            }
            var hi = mathFloor(a / BASE);
            var lo = a - hi * BASE;
            var digits = createArray(i + 2);
            digits[i + 1] = hi;
            digits[i + 0] = lo;
            return createBigInteger(sign, digits, i + 2);
        };

        var fromNumber = function(n) {
            if (mathFloor(n) !== n) {
                throw new RangeError("Cannot convert " + n + " to BigInteger");
            }
            if (n < BASE && 0 - n < BASE) {
                var a = createArray(1);
                a[0] = n < 0 ? 0 - n : 0 + n;
                return createBigInteger(n < 0 ? 1 : 0, a, n === 0 ? 0 : 1);
            }
            return fromHugeNumber(n);
        };

        var fromString = function(s) {
            var numLength = s[length];
            if (numLength === 0) {
                throw new RangeError();
            }
            var sign = 0;
            var signCharCode = s.charCodeAt(0);
            var from = 0;
            if (signCharCode === "+".charCodeAt(0)) {
                from = 1;
            }
            if (signCharCode === "-".charCodeAt(0)) {
                from = 1;
                sign = 1;
            }
            var radix = 10;
            if (from === 0 && numLength >= 2 && s.charCodeAt(0) === "0".charCodeAt(0)) {
                if (s.charCodeAt(1) === "b".charCodeAt(0)) {
                    radix = 2;
                    from = 2;
                } else if (s.charCodeAt(1) === "o".charCodeAt(0)) {
                    radix = 8;
                    from = 2;
                } else if (s.charCodeAt(1) === "x".charCodeAt(0)) {
                    radix = 16;
                    from = 2;
                }
            }
            numLength -= from;
            if (numLength === 0) {
                throw new RangeError();
            }

            var groupLength = 0;
            var groupRadix = 1;
            var limit = fastTrunc(BASE / radix);
            while (groupRadix <= limit) {
                groupLength += 1;
                groupRadix *= radix;
            }

            var size = mathFloor((numLength - 1) / groupLength) + 1;
            var magnitude = createArray(size);
            var start = from + 1 + (numLength - 1 - (size - 1) * groupLength) - groupLength;

            var j = -1;
            while (++j < size) {
                var groupStart = start + j * groupLength;
                var c = parseInteger(s, (groupStart >= from ? groupStart : from), groupStart + groupLength, radix);
                var l = -1;
                while (++l < j) {
                    var tmp = performMultiplication(c, magnitude[l], groupRadix);
                    var lo = tmp.lo;
                    var hi = tmp.hi;
                    magnitude[l] = lo;
                    c = hi;
                }
                magnitude[j] = c;
            }

            while (size > 0 && magnitude[size - 1] === 0) {
                size -= 1;
            }

            return createBigInteger(size === 0 ? 0 : sign, magnitude, size);
        };

        // mathPow(2, n) is slow in Chrome 93
        function exp(x, n) {
            var a = 1;
            while (n !== 0) {
                var q = (n >> 1);
                if (n !== (q << 1)) {
                    a *= x;
                }
                n = q;
                x *= x;
            }
            return a;
        }

        BigInteger.toNumber = function(a) {
            if (a.length === 0) {
                return 0;
            }
            if (a.length === 1) {
                return a.sign === 1 ? 0 - a.magnitude[0] : a.magnitude[0];
            }
            if (BASE + 1 !== BASE) {
                throw new RangeError();
            }
            var x = a.magnitude[a.length - 1];
            var y = a.magnitude[a.length - 2];
            var i = a.length - 3;
            while (i >= 0 && a.magnitude[i] === 0) {
                i -= 1;
            }
            if (i >= 0 && (x !== 1 && y % 2 === 0 || x === 1 && y % 2 === 1)) {
                y += 1;
            }
            var z = (x * BASE + y) * exp(BASE, a.length - 2);
            return a.sign === 1 ? 0 - z : z;
        };

        var compareMagnitude = function(a, b) {
            if (a === b) {
                return 0;
            }
            var c1 = a.length - b.length;
            if (c1 !== 0) {
                return c1 < 0 ? -1 : +1;
            }
            var i = a.length;
            while (--i >= 0) {
                var c = a.magnitude[i] - b.magnitude[i];
                if (c !== 0) {
                    return c < 0 ? -1 : +1;
                }
            }
            return 0;
        };

        var compareTo = function(a, b) {
            var c = a.sign === b.sign ? compareMagnitude(a, b) : 1;
            return a.sign === 1 ? 0 - c : c; // positive zero will be returned for c === 0
        };

        var addAndSubtract = function(a, b, isSubtraction) {
            var z = compareMagnitude(a, b);
            var resultSign = z < 0 ? (isSubtraction !== 0 ? 1 - b.sign : b.sign) : a.sign;
            var min = z < 0 ? a : b;
            var max = z < 0 ? b : a;
            // |a| <= |b|
            if (min.length === 0) {
                return createBigInteger(resultSign, max.magnitude, max.length);
            }
            var subtract = 0;
            var resultLength = max.length;
            if (a.sign !== (isSubtraction !== 0 ? 1 - b.sign : b.sign)) {
                subtract = 1;
                if (min.length === resultLength) {
                    while (resultLength > 0 && min.magnitude[resultLength - 1] === max.magnitude[resultLength - 1]) {
                        resultLength -= 1;
                    }
                }
                if (resultLength === 0) { // a === (-b)
                    return createBigInteger(0, createArray(0), 0);
                }
            }
            // result !== 0
            var result = createArray(resultLength + (1 - subtract));
            var i = -1;
            var c = 0;
            while (++i < min.length) {
                var aDigit = min.magnitude[i];
                c += max.magnitude[i] + (subtract !== 0 ? 0 - aDigit : aDigit - BASE);
                if (c < 0) {
                    result[i] = BASE + c;
                    c = 0 - subtract;
                } else {
                    result[i] = c;
                    c = 1 - subtract;
                }
            }
            i -= 1;
            while (++i < resultLength) {
                c += max.magnitude[i] + (subtract !== 0 ? 0 : 0 - BASE);
                if (c < 0) {
                    result[i] = BASE + c;
                    c = 0 - subtract;
                } else {
                    result[i] = c;
                    c = 1 - subtract;
                }
            }
            if (subtract === 0) {
                result[resultLength] = c;
                resultLength += c !== 0 ? 1 : 0;
            } else {
                while (resultLength > 0 && result[resultLength - 1] === 0) {
                    resultLength -= 1;
                }
            }
            return createBigInteger(resultSign, result, resultLength);
        };

        BigInteger.add = function(a, b) {
            return addAndSubtract(a, b, 0);
        };

        BigInteger.subtract = function(a, b) {
            return addAndSubtract(a, b, 1);
        };

        BigInteger.multiply = function(a, b) {
            if (a.length < b.length) {
                var tmp = a;
                a = b;
                b = tmp;
            }
            var alength = a.length;
            var blength = b.length;
            var am = a.magnitude;
            var bm = b.magnitude;
            var asign = a.sign;
            var bsign = b.sign;
            if (alength === 0 || blength === 0) {
                return createBigInteger(0, createArray(0), 0);
            }
            if (alength === 1 && am[0] === 1) {
                return createBigInteger(asign === 1 ? 1 - bsign : bsign, bm, blength);
            }
            if (blength === 1 && bm[0] === 1) {
                return createBigInteger(asign === 1 ? 1 - bsign : bsign, am, alength);
            }
            var astart = 0;
            while (am[astart] === 0) { // to optimize multiplications of a power of BASE
                astart += 1;
            }
            var resultSign = asign === 1 ? 1 - bsign : bsign;
            var resultLength = alength + blength;
            var result = createArray(resultLength);
            var i = -1;
            while (++i < blength) {
                var digit = bm[i];
                if (digit !== 0) { // to optimize multiplications by a power of BASE
                    var c = 0;
                    var j = astart - 1;
                    while (++j < alength) {
                        var carry = 1;
                        c += result[j + i] - BASE;
                        if (c < 0) {
                            c += BASE;
                            carry = 0;
                        }
                        var tmp = performMultiplication(c, am[j], digit);
                        var lo = tmp.lo;
                        var hi = tmp.hi;
                        result[j + i] = lo;
                        c = hi + carry;
                    }
                    result[alength + i] = c;
                }
            }
            if (result[resultLength - 1] === 0) {
                resultLength -= 1;
            }
            return createBigInteger(resultSign, result, resultLength);
        };

        var divideAndRemainder = function(a, b, isDivision) {
            if (b.length === 0) {
                throw new RangeError();
            }
            if (a.length === 0) {
                return createBigInteger(0, createArray(0), 0);
            }
            var quotientSign = a.sign === 1 ? 1 - b.sign : b.sign;
            if (b.length === 1 && b.magnitude[0] === 1) {
                if (isDivision !== 0) {
                    return createBigInteger(quotientSign, a.magnitude, a.length);
                }
                return createBigInteger(0, createArray(0), 0);
            }

            var divisorOffset = a.length + 1; // `+ 1` for extra digit in case of normalization
            var divisorAndRemainder = createArray(divisorOffset + b.length + 1); // `+ 1` to avoid `index < length` checks
            var divisor = divisorAndRemainder;
            var remainder = divisorAndRemainder;
            var n = -1;
            while (++n < a.length) {
                remainder[n] = a.magnitude[n];
            }
            var m = -1;
            while (++m < b.length) {
                divisor[divisorOffset + m] = b.magnitude[m];
            }

            var top = divisor[divisorOffset + b.length - 1];

            // normalization
            var lambda = 1;
            if (b.length > 1) {
                lambda = fastTrunc(BASE / (top + 1));
                if (lambda > 1) {
                    var carry = 0;
                    var l = -1;
                    while (++l < divisorOffset + b.length) {
                        var tmp = performMultiplication(carry, divisorAndRemainder[l], lambda);
                        var lo = tmp.lo;
                        var hi = tmp.hi;
                        divisorAndRemainder[l] = lo;
                        carry = hi;
                    }
                    divisorAndRemainder[divisorOffset + b.length] = carry;
                    top = divisor[divisorOffset + b.length - 1];
                }
                // assertion
                if (top < fastTrunc(BASE / 2)) {
                    throw new RangeError();
                }
            }

            var shift = a.length - b.length + 1;
            if (shift < 0) {
                shift = 0;
            }
            var quotient = void 0;
            var quotientLength = 0;

            // to optimize divisions by a power of BASE
            var lastNonZero = 0;
            while (divisor[divisorOffset + lastNonZero] === 0) {
                lastNonZero += 1;
            }

            var i = shift;
            while (--i >= 0) {
                var t = b.length + i;
                var q = BASE - 1;
                if (remainder[t] !== top) {
                    var tmp2 = performDivision(remainder[t], remainder[t - 1], top);
                    var q2 = tmp2.q;
                    //var r2 = tmp2.r;
                    q = q2;
                }

                var ax = 0;
                var bx = 0;
                var j = i - 1 + lastNonZero;
                while (++j <= t) {
                    var tmp3 = performMultiplication(bx, q, divisor[divisorOffset + j - i]);
                    var lo3 = tmp3.lo;
                    var hi3 = tmp3.hi;
                    bx = hi3;
                    ax += remainder[j] - lo3;
                    if (ax < 0) {
                        remainder[j] = BASE + ax;
                        ax = -1;
                    } else {
                        remainder[j] = ax;
                        ax = 0;
                    }
                }
                while (ax !== 0) {
                    q -= 1;
                    var c = 0;
                    var k = i - 1 + lastNonZero;
                    while (++k <= t) {
                        c += remainder[k] - BASE + divisor[divisorOffset + k - i];
                        if (c < 0) {
                            remainder[k] = BASE + c;
                            c = 0;
                        } else {
                            remainder[k] = c;
                            c = +1;
                        }
                    }
                    ax += c;
                }
                if (isDivision !== 0 && q !== 0) {
                    if (quotientLength === 0) {
                        quotientLength = i + 1;
                        quotient = createArray(quotientLength);
                    }
                    quotient[i] = q;
                }
            }

            if (isDivision !== 0) {
                if (quotientLength === 0) {
                    return createBigInteger(0, createArray(0), 0);
                }
                return createBigInteger(quotientSign, quotient, quotientLength);
            }

            var remainderLength = a.length + 1;
            if (lambda > 1) {
                var r = 0;
                var p = remainderLength;
                while (--p >= 0) {
                    var tmp4 = performDivision(r, remainder[p], lambda);
                    var q4 = tmp4.q;
                    var r4 = tmp4.r;
                    remainder[p] = q4;
                    r = r4;
                }
                if (r !== 0) {
                    // assertion
                    throw new RangeError();
                }
            }
            while (remainderLength > 0 && remainder[remainderLength - 1] === 0) {
                remainderLength -= 1;
            }
            if (remainderLength === 0) {
                return createBigInteger(0, createArray(0), 0);
            }
            var result = createArray(remainderLength);
            var o = -1;
            while (++o < remainderLength) {
                result[o] = remainder[o];
            }
            return createBigInteger(a.sign, result, remainderLength);
        };

        BigInteger.divide = function(a, b) {
            return divideAndRemainder(a, b, 1);
        };

        BigInteger.remainder = function(a, b) {
            return divideAndRemainder(a, b, 0);
        };

        BigInteger.unaryMinus = function(a) {
            return createBigInteger(a.length === 0 ? a.sign : 1 - a.sign, a.magnitude, a.length);
        };

        BigInteger.equal = function(a, b) {
            return compareTo(a, b) === 0;
        };
        BigInteger.lessThan = function(a, b) {
            return compareTo(a, b) < 0;
        };
        BigInteger.greaterThan = function(a, b) {
            return compareTo(a, b) > 0;
        };
        BigInteger.notEqual = function(a, b) {
            return compareTo(a, b) !== 0;
        };
        BigInteger.lessThanOrEqual = function(a, b) {
            return compareTo(a, b) <= 0;
        };
        BigInteger.greaterThanOrEqual = function(a, b) {
            return compareTo(a, b) >= 0;
        };

        BigInteger.exponentiate = function(a, b) {
            var n = BigInteger.toNumber(b);
            if (n < 0) {
                throw new RangeError();
            }
            if (n > 9007199254740991) {
                var y = BigInteger.toNumber(a);
                if (y === 0 || y === -1 || y === +1) {
                    return y === -1 && BigInteger.toNumber(BigInteger.remainder(b, BigInteger(2))) === 0 ? BigInteger.unaryMinus(a) : a;
                }
                throw new RangeError();
            }
            if (n === 0) {
                return BigInteger(1);
            }
            if (a.length === 1 && (a.magnitude[0] === 2 || a.magnitude[0] === 16)) {
                var bits = mathFloor(mathLog(BASE) / mathLog(2) + 0.5);
                var abits = mathFloor(mathLog(a.magnitude[0]) / mathLog(2) + 0.5);
                var nn = abits * n;
                var q = mathFloor(nn / bits);
                var r = nn - q * bits;
                var array = createArray(q + 1);
                array[q] = mathPow(2, r);
                return createBigInteger(a.sign === 0 || n % 2 === 0 ? 0 : 1, array, q + 1);
            }
            var x = a;
            while (n % 2 === 0) {
                n = mathFloor(n / 2);
                x = BigInteger.multiply(x, x);
            }
            var accumulator = x;
            n -= 1;
            if (n >= 2) {
                while (n >= 2) {
                    var t = mathFloor(n / 2);
                    if (t * 2 !== n) {
                        accumulator = BigInteger.multiply(accumulator, x);
                    }
                    n = t;
                    x = BigInteger.multiply(x, x);
                }
                accumulator = BigInteger.multiply(accumulator, x);
            }
            return accumulator;
        };

        BigInteger[prototype].toString = function(radix) {
            if (radix == void 0) {
                radix = 10;
            }
            if (radix !== 10 && (radix < 2 || radix > 36 || radix !== mathFloor(radix))) {
                throw new RangeError("radix argument must be an integer between 2 and 36");
            }

            if (this.length > 8 && true) { // https://github.com/GoogleChromeLabs/jsbi/blob/c9b179a4d5d34d35dd24cf84f7c1def54dc4a590/jsbi.mjs#L880
                if (this.sign === 1) {
                    return '-' + BigInteger.unaryMinus(this).toString(radix);
                }
                var s = mathFloor(this.length * mathLog(BASE) / mathLog(radix) / 2 + 0.5 - 1);
                var split = BigInteger.exponentiate(BigInteger(radix), BigInteger(s));
                var q = BigInteger.divide(this, split);
                var r = BigInteger.subtract(this, BigInteger.multiply(q, split));
                var a = r.toString(radix);
                return q.toString(radix) + '0'.repeat(s - a.length) + a;
            }

            var a = this;
            var result = a.sign === 1 ? "-" : "";

            var remainderLength = a.length;
            if (remainderLength === 0) {
                return "0";
            }
            if (remainderLength === 1) {
                result += a.magnitude[0].toString(radix);
                return result;
            }
            var groupLength = 0;
            var groupRadix = 1;
            var limit = fastTrunc(BASE / radix);
            while (groupRadix <= limit) {
                groupLength += 1;
                groupRadix *= radix;
            }
            // assertion
            if (groupRadix * radix <= BASE) {
                throw new RangeError();
            }
            var size = remainderLength + mathFloor((remainderLength - 1) / groupLength) + 1;
            var remainder = createArray(size);
            var n = -1;
            while (++n < remainderLength) {
                remainder[n] = a.magnitude[n];
            }

            var k = size;
            while (remainderLength !== 0) {
                var groupDigit = 0;
                var i = remainderLength;
                while (--i >= 0) {
                    var tmp = performDivision(groupDigit, remainder[i], groupRadix);
                    var q = tmp.q;
                    var r = tmp.r;
                    remainder[i] = q;
                    groupDigit = r;
                }
                while (remainderLength > 0 && remainder[remainderLength - 1] === 0) {
                    remainderLength -= 1;
                }
                k -= 1;
                remainder[k] = groupDigit;
            }
            result += remainder[k].toString(radix);
            while (++k < size) {
                var t = remainder[k].toString(radix);
                result += "0".repeat(groupLength - t.length) + t;
            }
            return result;
        };
        var signedRightShift = function(x, n) {
            // (!) it should work fast if n ~ size(x) - 53
            if (x.length === 0) {
                return x;
            }
            var shift = mathFloor(n / BASELOG2);
            var length = x.length - shift;
            if (length <= 0) {
                if (x.sign === 1) {
                    var minusOne = createArray(1);
                    minusOne[0] = 1;
                    return createBigInteger(1, minusOne, 1);
                }
                return createBigInteger(0, createArray(0), 0);
            }
            var digits = createArray(length + (x.sign === 1 ? 1 : 0));
            for (var i = 0; i < length; i += 1) {
                digits[i] = i + shift < 0 ? 0 : x.magnitude[i + shift];
            }
            n -= shift * BASELOG2;
            var s = exp(2, n);
            var s1 = mathFloor(BASE / s);
            var pr = 0;
            for (var i = length - 1; i >= 0; i -= 1) {
                var q = mathFloor(digits[i] / s);
                var r = digits[i] - q * s;
                digits[i] = q + pr * s1;
                pr = r;
            }
            if (length >= 1 && digits[length - 1] === 0) {
                length -= 1;
            }
            if (x.sign === 1) {
                var hasRemainder = pr > 0;
                for (var i = 0; i < shift && !hasRemainder; i += 1) {
                    hasRemainder = x.magnitude[i] !== 0;
                }
                if (hasRemainder) {
                    if (length === 0) {
                        length += 1;
                        digits[0] = 1;
                    } else {
                        // subtract one
                        var i = 0;
                        while (i < length && digits[i] === BASE - 1) {
                            digits[i] = 0;
                            i += 1;
                        }
                        if (i < length) {
                            digits[i] += 1;
                        } else {
                            length += 1;
                            digits[i] = 1;
                        }
                    }
                }
            }
            return createBigInteger(x.sign, digits, length);
        };
        BigInteger.signedRightShift = function(x, n) {
            return signedRightShift(x, BigInteger.toNumber(n));
        };
        BigInteger.leftShift = function(x, n) {
            return signedRightShift(x, 0 - BigInteger.toNumber(n));
        };

        var bitwiseArrayOp = function(a, b, opFn) {
            var maxLen = Math['max'](a.length, b.length);
            var result = createArray(maxLen);
            var i = -1;

            while (++i < maxLen) {
                var wordA = i < a.length ? a.magnitude[i] : 0;
                var wordB = i < b.length ? b.magnitude[i] : 0;
                var resultA = opFn(wordA & 0x3FFFFFFF, wordB & 0x3FFFFFFF);
                var resultB = opFn(mathFloor(wordA / mathPow(2, 30)), mathFloor(wordB / mathPow(2, 30)))
                result[i] = resultA + (resultB * mathPow(2, 30));
            }

            var resultLength = maxLen;
            while (resultLength > 0 && result[resultLength - 1] === 0) {
                resultLength -= 1;
            }

            return createBigInteger(0, result, resultLength);
        };

        BigInteger.bitwiseAnd = function(a, b) {
            return bitwiseArrayOp(a, b, function(x, y) {
                return x & y;
            });
        };

        BigInteger.bitwiseOr = function(a, b) {
            return bitwiseArrayOp(a, b, function(x, y) {
                return x | y;
            });
        };

        BigInteger.bitwiseXor = function(a, b) {
            return bitwiseArrayOp(a, b, function(x, y) {
                return x ^ y;
            });
        };
        BigInteger[prototype].valueOf = BigInteger[prototype].toNumber;

        return BigInteger;

    }());

    var sha256 = function(inbytes) {
        function rightRotate(value, amount) {
            return (value >>> amount) | (value << (32 - amount));
        };

        var mathPow = Math['pow'];
        var maxWord = mathPow(2, 32);
        var i, j;
        var result = [];

        var words = [];
        var asciiBitLength = inbytes[length] * 8;

        var hash = sha256.h = sha256.h || [];
        var k = sha256.k = sha256.k || [];
        var primeCounter = k[length];

        var isComposite = {};
        for (var candidate = 2; primeCounter < 64; candidate++) {
            if (!isComposite[candidate]) {
                for (i = 0; i < 313; i += candidate) {
                    isComposite[i] = candidate;
                }
                hash[primeCounter] = (mathPow(candidate, .5) * maxWord) | 0;
                k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
            }
        }

        var extra = ((55 - (inbytes[length] % 64) + 64) % 64 + 1);
        for (i = 0; i < inbytes[length] + extra; i++) {
            if (i < inbytes[length]) {
                j = inbytes[i];
            } else if (i > inbytes[length]) {
                j = 0;
            } else {
                j = 0x80;
            }
            words[i >> 2] |= j << ((3 - i) % 4) * 8;
        }
        words[words[length]] = ((asciiBitLength / maxWord) | 0);
        words[words[length]] = (asciiBitLength)

        for (j = 0; j < words[length];) {
            var w = words.slice(j, j += 16);
            var oldHash = hash;
            hash = hash.slice(0, 8);

            for (i = 0; i < 64; i++) {
                var i2 = i + j;
                var w15 = w[i - 15],
                    w2 = w[i - 2];

                var a = hash[0],
                    e = hash[4];
                var temp1 = hash[7] +
                    (rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25)) +
                    ((e & hash[5]) ^ ((~e) & hash[6])) +
                    k[i] +
                    (w[i] = (i < 16) ? w[i] : (
                        w[i - 16] +
                        (rightRotate(w15, 7) ^ rightRotate(w15, 18) ^ (w15 >>> 3)) +
                        w[i - 7] +
                        (rightRotate(w2, 17) ^ rightRotate(w2, 19) ^ (w2 >>> 10))
                    ) | 0);
                var temp2 = (rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22)) +
                    ((a & hash[1]) ^ (a & hash[2]) ^ (hash[1] & hash[2]));

                hash = [(temp1 + temp2) | 0].concat(hash);
                hash[4] = (hash[4] + temp1) | 0;
            }

            for (i = 0; i < 8; i++) {
                hash[i] = (hash[i] + oldHash[i]) | 0;
            }
        }

        for (i = 0; i < 8; i++) {
            for (j = 3; j + 1; j--) {
                var b = (hash[i] >> (j * 8)) & 255;
                result[result[length]] = b;
            }
        }
        return result;
    };

    var randState = [];
    var randBytes = function(count) {
        if (typeof process === 'object') return Array['from'](require('crypto')['randomBytes'](count));
        if (window.crypto) return Array[prototype]['slice'].call(window.crypto['getRandomValues'](new Uint8Array(count)));
        var bkey;
        var out = [];
        var randLen = randState[length];
        for (var i = 0; i <= count; i++) {
            if (i % 32 == 0 || i == count) {
                var block = ((i / 32) | 0) + (i == count);
                randState[randLen + 0] = (block >> 0) & 0xFF;
                randState[randLen + 1] = (block >> 8) & 0xFF;
                randState[randLen + 2] = (block >> 16) & 0xFF;
                randState[randLen + 3] = (block >> 24) & 0xFF;
                bkey = sha256(randState);
            }
            if (i != count) out[out[length]] = bkey[i % 32];
        }
        randState = bkey;
        return out;
    };
    if (typeof process !== 'object' && !window.crypto) {
        var mouseSeed = function(e){
            e = e || window['event'];
            var data = [e.clientX, e.clientY, e.screenX, e.screenY, new Date()['getTime']()];
            for (var i = 0; i < data[length]; i++) {
                randState[randState[length]] = (data[i] >> 0) & 0xFF;
                randState[randState[length]] = (data[i] >> 8) & 0xFF;
                randState[randState[length]] = (data[i] >> 16) & 0xFF;
                randState[randState[length]] = (data[i] >> 24) & 0xFF;
            }
            if (randState[length] > 512) randState = sha256(randState);
        };
        if (document.attachEvent) {
            document.attachEvent('onmousemove', mouseSeed);
        } else {
            document.addEventListener('mousemove', mouseSeed);
        }
    }

    var str2bytes = function(str) {
        var bytes = [];
        for (var i = 0; i < str[length]; i++) {
            var code = str.charCodeAt(i);
            bytes[bytes[length]] = code & 255
            bytes[bytes[length]] = code >> 8;
        }
        return bytes;
    }

    var bytes2str = function(bytes) {
        var str = "";
        for (var i = 0; i < bytes[length]; i += 2) {
            str += String.fromCharCode(bytes[i] | (bytes[i + 1] << 8));
        }
        return str;
    }

    var hex2bytes = function(str) {
        var bytes = [];
        var c = 0;
        if (str[length] % 2 != 0) {
            bytes[bytes[length]] = parseInt(str.substr(0, 1), 16);
            c = 1;
        }
        for (; c < str[length]; c += 2) {
            bytes[bytes[length]] = parseInt(str.substr(c, 2), 16);
        }
        return bytes;
    }

    var bytes2hex = function(bytes) {
        var str = "";
        for (var i = 0; i < bytes[length]; i++) {
            str += "0123456789ABCDEF".charAt(bytes[i] >> 4);
            str += "0123456789ABCDEF".charAt(bytes[i] & 0xF);
        }
        return str;
    }

    var encrypt = function(data, key, nonce, authLength) {
        var ikey = [];
        var out = [];
        if (typeof nonce == "number") {
            nonce = randBytes(nonce);
        }
        for (var i = 0; i < nonce[length]; i++) {
            ikey[ikey[length]] = nonce[i];
            out[out[length]] = nonce[i];
        }
        for (var i = 0; i < key[length]; i++) {
            ikey[ikey[length]] = key[i];
        }
        var ikeyc = ikey[length];
        var bkey = [];
        for (var i = 0; i < data[length]; i++) {
            if (i % 32 == 0) {
                var block = ((i / 32) | 0) + 1;
                ikey[ikeyc + 0] = (block >> 0) & 0xFF;
                ikey[ikeyc + 1] = (block >> 8) & 0xFF;
                ikey[ikeyc + 2] = (block >> 16) & 0xFF;
                ikey[ikeyc + 3] = (block >> 24) & 0xFF;
                bkey = sha256(ikey);
            }
            out[out[length]] = data[i] ^ bkey[i % 32];
        }
        ikey[ikeyc + 0] = 0;
        ikey[ikeyc + 1] = 0;
        ikey[ikeyc + 2] = 0;
        ikey[ikeyc + 3] = 0;
        var auth = sha256(sha256(ikey.concat(out.slice(nonce[length]))));
        for (var i = 0; i < authLength; i++) {
            out[out[length]] = auth[i];
        }
        return out;
    }

    var decrypt = function(data, key, nonceLength, authLength) {
        var ikey = [];
        var out = [];
        for (var i = 0; i < nonceLength; i++) {
            ikey[ikey[length]] = data[i];
        }
        for (var i = 0; i < key[length]; i++) {
            ikey[ikey[length]] = key[i];
        }
        var ikeyc = ikey[length];
        var bkey = [];
        ikey[ikeyc + 0] = 0;
        ikey[ikeyc + 1] = 0;
        ikey[ikeyc + 2] = 0;
        ikey[ikeyc + 3] = 0;
        var auth = sha256(sha256(ikey.concat(data.slice(nonceLength, data[length] - authLength))));
        var a = 0;
        for (var i = 0; i < authLength; i++) {
            a |= data[data[length] - authLength + i] ^ auth[i];
        }
        if (a) return null;
        for (var i = 0; i < data[length] - (nonceLength + authLength); i++) {
            if (i % 32 == 0) {
                var block = ((i / 32) | 0) + 1;
                ikey[ikeyc + 0] = (block >> 0) & 0xFF;
                ikey[ikeyc + 1] = (block >> 8) & 0xFF;
                ikey[ikeyc + 2] = (block >> 16) & 0xFF;
                ikey[ikeyc + 3] = (block >> 24) & 0xFF;
                bkey = sha256(ikey);
            }
            out[out[length]] = data[i + nonceLength] ^ bkey[i % 32];
        }
        return out;
    }

    var P = BigInteger.subtract(BigInteger.exponentiate(BigInteger(2), BigInteger(255)), BigInteger(19));
    var L = BigInteger("7237005577332262213973186563042994240857116359379907606001950938285454250989");
    var A = BigInteger(486662);

    var felem_add = function(a, b) {
        var res = BigInteger.add(a, b);
        return BigInteger.greaterThanOrEqual(res, P) ? BigInteger.subtract(res, P) : res;
    }

    var felem_sub = function(a, b) {
        var res = BigInteger.subtract(a, b);
        return BigInteger.lessThan(res, BigInteger(0)) ? BigInteger.add(res, P) : res;
    }

    var felem_mul = function(a, b) {
        return BigInteger.remainder(BigInteger.multiply(a, b), P);
    }

    var felem_inv = function(v) {
        var exp = BigInteger.subtract(P, BigInteger(2));
        var base = BigInteger.remainder(v, P);
        var res = BigInteger(1);
        while (BigInteger.greaterThan(exp, BigInteger(0))) {
            if (BigInteger.notEqual(BigInteger.remainder(exp, BigInteger(2)), BigInteger(0))) res = BigInteger.remainder(BigInteger.multiply(res, base), P);
            base = BigInteger.remainder(BigInteger.multiply(base, base), P);
            exp = BigInteger.signedRightShift(exp, BigInteger(1));
        }
        return res;
    }

    var cswap = function(swap, x_2, x_3) {
        var dummy = BigInteger.multiply(swap, BigInteger.bitwiseXor(x_2, x_3));
        return [BigInteger.bitwiseXor(x_2, dummy), BigInteger.bitwiseXor(x_3, dummy)];
    }

    var decodeLittleEndian = function(bytes) {
        var res = BigInteger(0);
        for (var i = 0; i < 32; i++) {
            res = BigInteger.bitwiseOr(res, BigInteger.leftShift(BigInteger(bytes[i]), BigInteger(i * 8)));
        }
        return res;
    }

    var encodeLittleEndian = function(num) {
        var bytes = [];
        var n = BigInteger(num);
        for (var i = 0; i < 32; i++) {
            bytes[bytes[length]] = Number(BigInteger.bitwiseAnd(n, BigInteger(0xFF)));
            n = BigInteger.signedRightShift(n, BigInteger(8));
        }
        return bytes;
    }

    var clampScalar = function(scalarBytes) {
        var b = scalarBytes.slice(0, 32);
        b[0] &= 248;
        b[31] &= 127;
        b[31] |= 64;
        return decodeLittleEndian(b);
    }

    var isIE = function() {
        var myNav = navigator['userAgent']['toLowerCase']();
        return (myNav.indexOf('msie') != -1) ? parseInt(myNav.split('msie')[1]) : false;
    }

    var nextTick = function(callback) {
        if (!isIE() || isIE() > 8) return callback();
        var docElem = document['documentElement'];
        var script = document.createElement("script");
        script[onreadystatechange] = function() {
            script[onreadystatechange] = null;
            docElem.removeChild(script);
            script = null;
            callback();
        };
        docElem.appendChild(script);
    }

    var montgomeryLadder = function(scalarBytes, pointBytes, callback) {
        var mustFixIE = isIE() && isIE() < 9;
        if (mustFixIE && !callback) {
            var out = showModalDialog("ladder_sync_ie.html", {"scalarBytes": scalarBytes, "pointBytes": pointBytes}, "dialogWidth:1px; dialogHeight:1px; dialogTop:99999px; dialogLeft:99999px;");
            var outFixed = new Array(out[length]);
            for (var i = 0; i < out[length]; i++) {
                outFixed[i] = out[i];
            }
            return outFixed;
        }

        var k = scalarBytes;
        var x_1 = BigInteger.remainder(decodeLittleEndian(pointBytes), P);

        var x_2 = BigInteger(1),
            z_2 = BigInteger(0);
        var x_3 = x_1,
            z_3 = BigInteger(1);
        var swap = BigInteger(0);

        var t = 255;

        var loopStep = function () {
            var iterationsPerTick = mustFixIE ? 32 : Infinity;
            var end = Math['max'](t - iterationsPerTick, -1);

            while (t > end) {
                var k_t = BigInteger.bitwiseAnd(BigInteger.signedRightShift(k, BigInteger(t)), BigInteger(1));
                var swapped = cswap(BigInteger.bitwiseXor(swap, k_t), x_2, x_3);
                x_2 = swapped[0];
                x_3 = swapped[1];
                swapped = cswap(BigInteger.bitwiseXor(swap, k_t), z_2, z_3);
                z_2 = swapped[0];
                z_3 = swapped[1];
                swap = k_t;

                var A_val = felem_add(x_2, z_2);
                var AA = felem_mul(A_val, A_val);
                var B_val = felem_sub(x_2, z_2);
                var BB = felem_mul(B_val, B_val);
                var E = felem_sub(AA, BB);

                var C_val = felem_add(x_3, z_3);
                var D_val = felem_sub(x_3, z_3);
                var DA = felem_mul(D_val, A_val);
                var CB = felem_mul(C_val, B_val);

                var add_val = felem_add(DA, CB);
                var sub_val = felem_sub(DA, CB);

                x_3 = felem_mul(add_val, add_val);
                var z3_tmp = felem_mul(sub_val, sub_val);
                z_3 = felem_mul(z3_tmp, x_1);

                x_2 = felem_mul(AA, BB);
                var a24_E = felem_mul(E, BigInteger(121665));
                var AA_a24E = felem_add(AA, a24_E);
                z_2 = felem_mul(E, AA_a24E);

                t--;
            }

            if (t >= 0) {
                nextTick(loopStep);
            } else {
                var swapped = cswap(swap, x_2, x_3);
                x_2 = swapped[0];
                x_3 = swapped[1];
                swapped = cswap(swap, z_2, z_3);
                z_2 = swapped[0];
                z_3 = swapped[1];

                var z2_inv = felem_inv(z_2);
                var result = felem_mul(x_2, z2_inv);

                if (!callback) return encodeLittleEndian(result);
                callback(encodeLittleEndian(result));
            }
        }

        return nextTick(loopStep);
    };

    var basePoint = [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

    var x25519 = function(scalarBytes, pointBytes) {
        return montgomeryLadder(clampScalar(scalarBytes), pointBytes);
    }

    var getPublicKey = function(privateKeyBytes) {
        return x25519(privateKeyBytes, basePoint);
    }

    var hashToScalar = function(dataBytes) {
        var digestBytes = sha256(dataBytes);
        var hashBigInt = BigInteger(0);
        for (var i = 0; i < digestBytes[length]; i++) {
            hashBigInt = BigInteger.add(BigInteger.leftShift(hashBigInt, BigInteger(8)), BigInteger(digestBytes[i]));
        }
        return BigInteger.remainder(hashBigInt, L);
    }

    var sign = function(privateKeyBytes, messageBytes) {
        var d = clampScalar(privateKeyBytes);

        var rInput = privateKeyBytes.concat(messageBytes);
        var r = hashToScalar(rInput);

        var xR = montgomeryLadder(r, basePoint);

        var pubKey = getPublicKey(privateKeyBytes);
        var cInput = xR.concat(pubKey).concat(messageBytes);
        var c = hashToScalar(cInput);

        var cd = BigInteger.remainder(BigInteger.multiply(c, d), L);
        var s = BigInteger.remainder(BigInteger.add(r, cd), L);

        return xR.concat(encodeLittleEndian(s));
    }

    var verify = function(publicKeyBytes, signature, messageBytes) {
        var xR = signature.slice(0, 32);
        var sBytes = signature.slice(32, 64);
        var s = decodeLittleEndian(sBytes);

        if (BigInteger.greaterThanOrEqual(s, L)) return false;

        var cInput = xR.concat(publicKeyBytes).concat(messageBytes);
        var c = hashToScalar(cInput);

        var xS_bytes = montgomeryLadder(s, basePoint);
        var xC_bytes = montgomeryLadder(c, publicKeyBytes);

        var x1 = decodeLittleEndian(xS_bytes);
        var x2 = decodeLittleEndian(xC_bytes);
        var Z = decodeLittleEndian(xR);

        var x1x2 = felem_mul(x1, x2);

        var diff_x = felem_sub(x1, x2);
        var diff_x_sq = felem_mul(diff_x, diff_x);
        var part_A = felem_mul(diff_x_sq, felem_mul(Z, Z));

        var sum_x = felem_add(x1, x2);
        var inner_1 = felem_mul(felem_add(x1x2, BigInteger(1)), sum_x);
        var inner_2 = felem_mul(felem_mul(BigInteger(2), A), x1x2);
        var sum_inner = felem_add(inner_1, inner_2);
        var part_B = felem_mul(felem_mul(BigInteger(2), sum_inner), Z);

        var term_minus_1 = felem_sub(x1x2, BigInteger(1));
        var part_C = felem_mul(term_minus_1, term_minus_1);

        var V = felem_add(felem_sub(part_A, part_B), part_C);

        return BigInteger.equal(V, BigInteger(0));
    }

    var SymmetricKey = function(value) {
        if (!value) {
            value = randBytes(32);
        } else if (typeof value == "string") {
            value = hex2bytes(value);
        }
        if (value[length] != 32) {
            throw new TypeError("Invalid symmetric key");
        }
        this.value = value;
    }

    SymmetricKey[prototype]["encrypt"] = function(data) {
        return encrypt(data, this.value, 16, 16);
    }

    SymmetricKey[prototype]["decrypt"] = function(data) {
        return decrypt(data, this.value, 16, 16);
    }

    SymmetricKey[prototype]["toString"] = function() {
        return bytes2hex(this.value);
    }

    var PublicKey = function(value) {
        if (typeof value == "string") {
            value = hex2bytes(value);
        }
        if (value[length] != 32) {
            throw new TypeError("Invalid public key");
        }
        this.value = value;
    }

    var KeyPair = function(value) {
        if (!value) {
            value = randBytes(32);
        } else if (typeof value == "string") {
            value = hex2bytes(value);
        }
        if (value[length] != 32) {
            throw new TypeError("Invalid private key");
        }
        this.value = value;
        this['public'] = new PublicKey(getPublicKey(this.value));
    }

    PublicKey[prototype]["toString"] = function() {
        return bytes2hex(this.value);
    }

    KeyPair[prototype]["toString"] = function() {
        return bytes2hex(this.value);
    }

    PublicKey[prototype]["encrypt"] = function(data) {
        var tempKey = new KeyPair();
        var cryptKey = x25519(tempKey.value, this.value);
        var ciphertext = encrypt(data, cryptKey, 0, 16);
        return [].concat(tempKey['public'].value, ciphertext);
    }

    KeyPair[prototype]["decrypt"] = function(data) {
        var cryptKey = x25519(this.value, data.slice(0, 32));
        return decrypt(data.slice(32), cryptKey, 0, 16);
    }

    PublicKey[prototype]["verify"] = function(signature, data) {
        return verify(this.value, signature, data);
    }

    KeyPair[prototype]["sign"] = function(data) {
        return sign(this.value, data);
    }

    KeyPair[prototype]["exchange"] = function(pub) {
        return new SymmetricKey(x25519(this.value, pub.value));
    }

    var uCrypt = {
        "internal": {
            "montgomeryLadder": montgomeryLadder
        },
        "util": {
            "bytes2str": bytes2str,
            "str2bytes": str2bytes,
            "bytes2hex": bytes2hex,
            "hex2bytes": hex2bytes
        },
        "SymmetricKey": SymmetricKey,
        "KeyPair": KeyPair,
        "PublicKey": PublicKey
    };


    if (typeof module !== "undefined" && module.hasOwnProperty("exports")) {
        module.exports = uCrypt;
    } else {
        window.uCrypt = uCrypt;
    }
})();