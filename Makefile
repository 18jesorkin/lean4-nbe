
default:
	lake exe cache get
	lake build
	lake exe textbook

show: default
	python3 -m http.server 8880 --directory _out/html-single &
	open http://localhost:8880/

clean:
	lake clean
	rm -rf _out
