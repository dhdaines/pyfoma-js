import { defineConfig } from "vite";

export default defineConfig({
    root: "demo",
    base: "/pyfoma-js",
    build: {
        emptyOutDir: true,
        outDir: "../site",
        target: "es2015",
        chunkSizeWarningLimit: 1500,
    }
});
