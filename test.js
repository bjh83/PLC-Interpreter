class A {
	var x = 6;
	var y = 7;

	prod() {
		throw 5;
		return this.x * this.y;
	}

	set2(a, b) {
		x = a;
		y = b;
	}
}

class B extends A {
	set1(a) {
		set2(a, a);
	}

	static main () {
		var b = new B();
		b.set1(10);
		try {
			return b.prod();
		} catch(e) {
			return 4;
		}
	}
}
